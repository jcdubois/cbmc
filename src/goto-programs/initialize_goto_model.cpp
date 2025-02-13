/*******************************************************************\

Module: Get a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "initialize_goto_model.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/message.h>
#include <util/options.h>
#include <util/unicode.h>

#include <goto-programs/rebuild_goto_start_function.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <langapi/language.h>
#include <langapi/language_file.h>
#include <langapi/mode.h>
#include <linking/static_lifetime_init.h>

#include "read_goto_binary.h"

#include <fstream>

/// Generate an entry point that calls a function with the given name, based on
/// the functions language mode in the symbol table
static bool generate_entry_point_for_function(
  const optionst &options,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  const irep_idt &entry_function_name = options.get_option("function");
  CHECK_RETURN(!entry_function_name.empty());
  auto matches = symbol_table.match_name_or_base_name(entry_function_name);
  // it's ok if this is ambiguous at this point, we just need to get a mode, the
  // actual entry point generator will take care of resolving (or rejecting)
  // ambiguity
  if(matches.empty())
  {
    throw invalid_command_line_argument_exceptiont{
      std::string("couldn't find entry with name '") +
        id2string(entry_function_name) + "' in symbol table",
      "--function"};
  }
  const auto &entry_point_mode = matches.front()->second.mode;
  PRECONDITION(!entry_point_mode.empty());
  auto const entry_language = get_language_from_mode(entry_point_mode);
  CHECK_RETURN(entry_language != nullptr);
  entry_language->set_language_options(options, message_handler);
  return entry_language->generate_support_functions(
    symbol_table, message_handler);
}

void initialize_from_source_files(
  const std::list<std::string> &sources,
  const optionst &options,
  language_filest &language_files,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(sources.empty())
    return;

  messaget msg(message_handler);

  for(const auto &filename : sources)
  {
    std::ifstream infile(widen_if_needed(filename));

    if(!infile)
    {
      throw system_exceptiont("Failed to open input file '" + filename + '\'');
    }

    language_filet &lf = language_files.add_file(filename);
    lf.language = get_language_from_filename(filename);

    if(lf.language == nullptr)
    {
      throw invalid_command_line_argument_exceptiont{
        "Failed to figure out type of file", filename};
    }

    languaget &language = *lf.language;
    language.set_language_options(options, message_handler);

    msg.progress() << "Parsing " << filename << messaget::eom;

    if(language.parse(infile, filename, message_handler))
    {
      throw invalid_input_exceptiont("PARSING ERROR");
    }

    lf.get_modules();
  }

  msg.progress() << "Converting" << messaget::eom;

  if(language_files.typecheck(symbol_table, message_handler))
  {
    throw invalid_input_exceptiont("CONVERSION ERROR");
  }
}

void set_up_custom_entry_point(
  language_filest &language_files,
  symbol_tablet &symbol_table,
  const std::function<std::size_t(const irep_idt &)> &unload,
  const optionst &options,
  bool try_mode_lookup,
  message_handlert &message_handler)
{
  bool binaries_provided_start =
    symbol_table.has_symbol(goto_functionst::entry_point());

  bool entry_point_generation_failed=false;

  if(binaries_provided_start && options.is_set("function"))
  {
    // The goto binaries provided already contain a __CPROVER_start
    // function that may be tied to a different entry point `function`.
    // Hence, we will rebuild the __CPROVER_start function.

    // Get the language annotation of the existing __CPROVER_start function.
    std::unique_ptr<languaget> language =
      get_entry_point_language(symbol_table, options, message_handler);

    // To create a new entry point we must first remove the old one
    remove_existing_entry_point(symbol_table);

    // Create the new entry-point
    entry_point_generation_failed =
      language->generate_support_functions(symbol_table, message_handler);

    // Remove the function from the goto functions so it is copied back in
    // from the symbol table during goto_convert
    if(!entry_point_generation_failed)
      unload(goto_functionst::entry_point());
  }
  else if(!binaries_provided_start)
  {
    if(try_mode_lookup && options.is_set("function"))
    {
      // no entry point is present; Use the mode of the specified entry function
      // to generate one
      entry_point_generation_failed = generate_entry_point_for_function(
        options, symbol_table, message_handler);
    }
    if(
      !try_mode_lookup || entry_point_generation_failed ||
      !options.is_set("function"))
    {
      // Allow all language front-ends to try to provide the user-specified
      // (--function) entry-point, or some language-specific default:
      entry_point_generation_failed = language_files.generate_support_functions(
        symbol_table, message_handler);
    }
  }

  if(entry_point_generation_failed)
  {
    throw invalid_input_exceptiont("SUPPORT FUNCTION GENERATION ERROR");
  }
}

goto_modelt initialize_goto_model(
  const std::vector<std::string> &files,
  message_handlert &message_handler,
  const optionst &options)
{
  messaget msg(message_handler);
  if(files.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "missing program argument",
      "filename",
      "one or more paths to program files");
  }

  std::list<std::string> binaries, sources;

  for(const auto &file : files)
  {
    if(is_goto_binary(file, message_handler))
      binaries.push_back(file);
    else
      sources.push_back(file);
  }

  language_filest language_files;
  goto_modelt goto_model;
  initialize_from_source_files(
    sources, options, language_files, goto_model.symbol_table, message_handler);

  if(read_objects_and_link(binaries, goto_model, message_handler))
    throw incorrect_goto_program_exceptiont{"failed to read/link goto model"};

  set_up_custom_entry_point(
    language_files,
    goto_model.symbol_table,
    [&goto_model](const irep_idt &id) { return goto_model.unload(id); },
    options,
    true,
    message_handler);

  if(language_files.final(goto_model.symbol_table))
  {
    throw invalid_input_exceptiont("FINAL STAGE CONVERSION ERROR");
  }

  msg.status() << "Generating GOTO Program" << messaget::eom;

  goto_convert(
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);

  if(options.is_set("validate-goto-model"))
  {
    goto_model_validation_optionst goto_model_validation_options{
      goto_model_validation_optionst ::set_optionst::all_false};

    goto_model.validate(
      validation_modet::INVARIANT, goto_model_validation_options);
  }

  // stupid hack
  config.set_object_bits_from_symbol_table(
    goto_model.symbol_table);

  return goto_model;
}

void update_max_malloc_size(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  if(!goto_model.symbol_table.has_symbol(CPROVER_PREFIX "max_malloc_size"))
    return;

  const auto previous_max_malloc_size_value = numeric_cast<mp_integer>(
    goto_model.symbol_table.lookup_ref(CPROVER_PREFIX "max_malloc_size").value);
  const mp_integer current_max_malloc_size = config.max_malloc_size();

  if(
    !previous_max_malloc_size_value.has_value() ||
    *previous_max_malloc_size_value != current_max_malloc_size)
  {
    symbolt &max_malloc_size_sym = goto_model.symbol_table.get_writeable_ref(
      CPROVER_PREFIX "max_malloc_size");
    max_malloc_size_sym.value =
      from_integer(current_max_malloc_size, size_type());
    max_malloc_size_sym.value.set(ID_C_no_nondet_initialization, true);

    if(goto_model.can_produce_function(INITIALIZE_FUNCTION))
      recreate_initialize_function(goto_model, message_handler);
  }
}
