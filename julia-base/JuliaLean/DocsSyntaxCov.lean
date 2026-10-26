import JuliaLean.Registry.Types
import JuliaLean.DocsSyntaxCov.DocsCoreProps
import JuliaLean.DocsSyntaxCov.DocsProps
import JuliaLean.DocsSyntaxCov.ParseProps
import JuliaLean.DocsSyntaxCov.TomlLexProps
import JuliaLean.DocsSyntaxCov.TomlPrintTables
import JuliaLean.DocsSyntaxCov.LinkingProps
import JuliaLean.DocsSyntaxCov.SyntaxProps
import JuliaLean.DocsSyntaxCov.BinaryProps
import JuliaLean.DocsSyntaxCov.Rows
import JuliaLean.Toml.Proven
import JuliaLean.Platforms

namespace JuliaLean.DocsSyntaxCov

open JuliaLean.Registry

private def proven (id file : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, source, status := .proven,
    prop, thm := some thm }

private def refuted (id file : String) (fns : List String) (statement source issue notes : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, source, status := .refuted,
    prop, thm := some thm, issue, notes }

/-- Registry entries of this area. -/
def entries : List Entry := [
  proven "docssyntaxcov-docs-signature-implementation" "base/docs/Docs.jl"
    ["signature!", "signature", "argtype", "tvar"]
    "The signature helpers return or throw according to their mirrored recursive bodies."
    "base/docs/Docs.jl:100-147; exact implementation equations"
    ``SignatureImplementation ``signatureImplementation,
  proven "docssyntaxcov-docs-signature-forms" "base/docs/Docs.jl"
    ["signature!", "signature", "argtype", "tvar"]
    "Signatures for calls, optional arguments, varargs, macros and where clauses have the documented tuple forms."
    "base/docs/Docs.jl:100-147; MultiDoc signature invariant"
    ``SignatureForms ``signatureForms,
  refuted "docssyntaxcov-doc-signature-typevar" "base/docs/Docs.jl" ["signature!", "signature"]
    "A where type variable must not add an unrelated positional Tuple alternative."
    "base/docs/Docs.jl:100-128; method-signature invariant"
    "none found (queries: Docs signature where, doc lookup where clause, docstring signature typevar)"
    "signature adds Tuple{T}, causing a Vector method docstring to match Tuple{Int}."
    ``DocSignatureTypevar ``docSignatureTypevar_refuted,
  proven "docssyntaxcov-docs-meta" "base/docs/Docs.jl" ["meta", "initmeta"]
    "Documentation metadata is created only when requested and existing dictionaries are preserved."
    "base/docs/Docs.jl:80-98" ``MetaForms ``metaForms,
  proven "docssyntaxcov-docs-docstr" "base/docs/Docs.jl"
    ["docstr", "_docstr", "docexpr", "MultiDoc"]
    "DocStr constructors preserve text, objects and metadata, and MultiDoc starts empty."
    "base/docs/Docs.jl:170-225" ``DocstrForms ``docstrForms,
  proven "docssyntaxcov-docs-docstr-lookup" "base/docs/Docs.jl" ["docstr(::Binding)"]
    "Binding doc lookup returns the exact requested signature from the first module containing it."
    "base/docs/Docs.jl:170-183" ``DocstrLookupBehavior ``docstrLookupBehavior,
  proven "docssyntaxcov-docs-register" "base/docs/Docs.jl" ["doc!"]
    "doc! stores the binding and signature, appends new signatures and preserves replaced order."
    "base/docs/Docs.jl:236-262" ``DocRegisterStores ``docRegisterStores,
  proven "docssyntaxcov-docs-names" "base/docs/Docs.jl" ["namify", "astname", "macroname"]
    "Documented names are extracted from every supported definition and macro form."
    "base/docs/Docs.jl:297-334" ``NamifyForms ``namifyForms,
  proven "docssyntaxcov-docs-isfield" "base/docs/Docs.jl" ["isfield"]
    "isfield recognizes dotted symbol chains and rejects other expressions."
    "base/docs/Docs.jl:336-338" ``IsfieldForms ``isfieldForms,
  refuted "docssyntaxcov-field-doc-const" "base/docs/Docs.jl" ["metadata"]
    "A field docstring attaches to the field immediately following it, including const fields."
    "base/docs/Docs.jl:343-392; Julia manual field-docstring syntax"
    "#58820 (open, duplicate); queries: field docstring const, struct field documentation const field"
    "A const field is skipped and its docstring attaches to the next ordinary field."
    ``FieldDocsAttach ``fieldDocsAttach_refuted,
  proven "docssyntaxcov-docs-fields" "base/docs/Docs.jl" ["metadata"]
    "Plain and typed field declarations receive the preceding field docstring."
    "base/docs/Docs.jl:355-392" ``FieldDocsPlain ``fieldDocsPlain,
  proven "docssyntaxcov-docs-metadata" "base/docs/Docs.jl" ["metadata"]
    "metadata records the source, module and module-document flag."
    "base/docs/Docs.jl:355-392" ``MetadataForms ``metadataForms,
  proven "docssyntaxcov-docs-builders" "base/docs/Docs.jl"
    ["keyworddoc", "objectdoc", "calldoc", "callargs", "validcall"]
    "Documentation expression builders preserve definitions and compute their signatures."
    "base/docs/Docs.jl:394-439" ``BuilderForms ``builderForms,
  proven "docssyntaxcov-docs-module-multidoc" "base/docs/Docs.jl" ["moduledoc", "multidoc"]
    "Module and tuple docstrings expand according to their complete method bodies."
    "base/docs/Docs.jl:441-483" ``ModuleMultiDocBehavior ``moduleMultiDocBehavior,
  proven "docssyntaxcov-docs-finddoc" "base/docs/Docs.jl" ["__doc__!", "replace_meta_doc", "finddoc"]
    "@__doc__ markers are found in order and replaced by @doc calls."
    "base/docs/Docs.jl:549-601" ``FinddocForms ``finddocForms,
  proven "docssyntaxcov-docs-predicates" "base/docs/Docs.jl"
    ["isquotedmacrocall", "isbasicdoc", "is_signature", "iscallexpr"]
    "The doc macro predicates recognize exactly their supported expression shapes."
    "base/docs/Docs.jl:608-614,686-687" ``DocmPredicates ``docmPredicates,
  proven "docssyntaxcov-docs-lookup" "base/docs/Docs.jl" ["getdoc", "catdoc", "_doc(::Binding)"]
    "Dynamic getdoc results take precedence and catdoc concatenates its inputs."
    "base/docs/Docs.jl:283-293,616-637" ``DocLookupForms ``docLookupForms,
  proven "docssyntaxcov-docs-targets" "base/docs/Docs.jl" ["_doc(::UnionAll)", "_doc(::Any)"]
    "Object documentation resolves the object's binding and tuple signature."
    "base/docs/Docs.jl:640-642" ``DocTargetForms ``docTargetForms,
  proven "docssyntaxcov-docs-simple-lookup" "base/docs/Docs.jl" ["simple_lookup_doc"]
    "Single-argument @doc lookup chooses keyword, binding or type documentation."
    "base/docs/Docs.jl:644-667" ``SimpleLookupForms ``simpleLookupForms,
  proven "docssyntaxcov-docs-docm" "base/docs/Docs.jl" ["docm", "_docm", "multidoc"]
    "@doc dispatches keywords, definitions, tuples, errors and macroexpanded forms to the matching builder."
    "base/docs/Docs.jl:669-790" ``DocmDispatch ``docmDispatch,
  proven "docssyntaxcov-docs-docerror" "base/docs/Docs.jl" ["docerror"]
    "docerror names the rejected expression and adds the macro hint only for macro calls."
    "base/docs/Docs.jl:792-801" ``DocerrorForm ``docerrorForm,
  proven "docssyntaxcov-docs-loaddocs" "base/docs/Docs.jl" ["loaddocs"]
    "Bootstrap documentation records are replayed newest first in their own modules."
    "base/docs/Docs.jl:808-819" ``LoaddocsOrder ``loaddocsOrder,
  proven "docssyntaxcov-docs-hasdoc-ref" "base/docs/Docs.jl" ["hasdoc", "ref"]
    "Module hasdoc delegates through Binding and @ref builds the binding-signature lookup."
    "base/docs/Docs.jl:192-196,864-875" ``RefAndHasdoc ``refAndHasdoc,
  proven "docssyntaxcov-docs-hasdoc-binding" "base/docs/Docs.jl" ["hasdoc(::Binding)"]
    "hasdoc detects dynamic docs, META entries and documented aliases."
    "base/docs/Docs.jl:865-875" ``HasdocForms ``hasdocForms,
  proven "docssyntaxcov-docs-undocumented" "base/docs/Docs.jl" ["undocumented_names"]
    "undocumented_names returns exactly eligible names lacking documentation."
    "base/docs/Docs.jl:888-893" ``UndocumentedNamesSpec ``undocumentedNamesSpec,

  proven "docssyntaxcov-bindings-normalise" "base/docs/bindings.jl" ["Binding"]
    "Binding normalizes self names and binding modules."
    "base/docs/bindings.jl:7-25" ``BindingNormalise ``bindingNormalise,
  proven "docssyntaxcov-bindings-import" "base/docs/bindings.jl" ["Binding"]
    "Binding follows explicit import chains."
    "base/docs/bindings.jl:7-25" ``BindingFollowsImport ``bindingFollowsImport,
  proven "docssyntaxcov-bindings-split" "base/docs/bindings.jl" ["bindingexpr", "splitexpr"]
    "Binding expressions split dotted names, symbols and GlobalRefs."
    "base/docs/bindings.jl:28-38" ``SplitexprForms ``splitexprForms,
  proven "docssyntaxcov-bindings-accessors" "base/docs/bindings.jl" ["defined", "resolve", "show"]
    "Binding accessors check definition, resolve values and display qualified names."
    "base/docs/bindings.jl:30-53" ``BindingAccessors ``bindingAccessors,
  proven "docssyntaxcov-bindings-alias" "base/docs/bindings.jl" ["aliasof"]
    "aliasof follows type, function and module aliases and preserves other bindings."
    "base/docs/bindings.jl:55-59" ``AliasofForms ``aliasofForms,

  proven "docssyntaxcov-utils-render" "base/docs/utils.jl" ["HTML", "show", "html_str", "catdoc", "print", "text_str"]
    "HTML and Text construction, rendering and concatenation preserve their content."
    "base/docs/utils.jl:33-93,109-119" ``HtmlTextRendering ``htmlTextRendering,
  proven "docssyntaxcov-utils-equality" "base/docs/utils.jl" ["==", "hash"]
    "Wrapper equality and hashing call the corresponding content operations."
    "base/docs/utils.jl:95-96" ``WrapperEqContent ``wrapperEqContent,
  refuted "docssyntaxcov-text-hash-isequal" "base/docs/utils.jl" ["==", "hash"]
    "isequal wrappers must have equal hashes."
    "base/hashing.jl hash contract"
    "none found (queries: HTML hash isequal, Text hash, Docs.Text hash)"
    "Text(-0.0) and Text(0.0) are isequal but have different hashes."
    ``TextHashIsequal ``textHashIsequal_refuted,

  proven "docssyntaxcov-core-records" "base/docs/core.jl" ["DocLinkedList", "doc!"]
    "CoreDocs constructors and doc! prepend the exact record."
    "base/docs/core.jl:10-19" ``CoreDocsRecords ``coreDocsRecords,
  proven "docssyntaxcov-core-expr" "base/docs/core.jl" ["isexpr", "lazy_iterpolate"]
    "Core expression tests and lazy interpolation follow their expression branches."
    "base/docs/core.jl:21-24" ``CoreExprHelpers ``coreExprHelpers,
  proven "docssyntaxcov-core-docm" "base/docs/core.jl" ["docm"]
    "Bootstrap @doc expansion orders definition and registration correctly."
    "base/docs/core.jl:26-37" ``CoreDocmExpansion ``coreDocmExpansion,
  proven "docssyntaxcov-basedocs-keyword" "base/docs/basedocs.jl" ["kw_str"]
    "kw_str constructs the named documentation keyword."
    "base/docs/basedocs.jl:11-13" ``KwStrKeyword ``kwStrKeyword,

  proven "docssyntaxcov-parse-union" "base/parse.jl" ["parse(::Union{})", "tryparse(::Union{})"]
    "Parsing Union{} always throws the documented error."
    "base/parse.jl:37,263" ``Parse.ParseUnionAllThrows ``Parse.parseUnionAllThrows,
  proven "docssyntaxcov-parse-char" "base/parse.jl" ["parse(::AbstractChar)"]
    "Character digits and bases are accepted exactly in their documented ranges."
    "base/parse.jl:39-47" ``Parse.ParseCharDigits ``Parse.parseCharDigits,
  proven "docssyntaxcov-parse-whitespace" "base/parse.jl"
    ["isspace_ascii", "skipspacechar", "skipspacechar_back", "skipspace", "skipspace_back", "parseint_preamble", "parseint_utf8", "throw_parseint_error"]
    "Whitespace and integer helpers mirror the shared integer-parser bodies."
    "base/parse.jl:53-171" ``Parse.WhitespaceAndIntegerMethods ``Parse.whitespaceAndIntegerMethods,
  proven "docssyntaxcov-parse-int-range" "base/parse.jl" ["tryparse_internal(::Integer)", "check_valid_base"]
    "Integer range parsing uses the requested byte range and validates bases 2 through 62."
    "base/parse.jl:173-182,234-239" ``Parse.TryparseInternalIntRange ``Parse.tryparseInternalIntRange,
  proven "docssyntaxcov-parse-int-string" "base/parse.jl" ["parseint_string", "parse", "tryparse"]
    "Integer string parsing consumes the whole string with prefix base detection."
    "base/parse.jl:247-263" ``Parse.ParseintStringWhole ``Parse.parseintStringWhole,
  refuted "docssyntaxcov-parse-bool-leading-space" "base/parse.jl" ["tryparse_internal(::Bool)", "parse(::Bool)", "tryparse(::Bool)"]
    "Leading whitespace is accepted for numeric Bool forms as it is for trailing whitespace."
    "base/parse.jl:184-232"
    "#42616 (closed, related); queries: parse Bool whitespace, parse Bool leading space, tryparse Bool"
    "parse(Bool, \" 1\") throws while \"1 \" succeeds."
    ``Parse.BoolLeadingSpace ``Parse.boolLeadingSpace_refuted,
  proven "docssyntaxcov-parse-wrappers" "base/parse.jl" ["tryparse", "parse", "tryparse_internal"]
    "Bool, float and real wrappers delegate to the exact internal ranges and raise policy."
    "base/parse.jl:247-280,346-374" ``Parse.ParseWrapperMethods ``Parse.parseWrapperMethods,
  proven "docssyntaxcov-parse-real" "base/parse.jl" ["tryparse_internal(::Real)", "_parse_failure", "parse(::Real)"]
    "Real parsing trims the documented range and converts failure to ArgumentError."
    "base/parse.jl:346-374" ``Parse.FloatAndRealFallbacks ``Parse.floatAndRealFallbacks,
  refuted "docssyntaxcov-parse-complex-trailing" "base/parse.jl" ["tryparse_internal(::Complex)", "parse(::Complex)", "tryparse(::Complex)"]
    "Complex parsing rejects characters after the imaginary unit."
    "base/parse.jl:284-343"
    "none found (queries: parse complex, Complex parse im, parse Complex trailing characters)"
    "Characters after the last imaginary unit are ignored."
    ``Parse.ComplexTrailingRejected ``Parse.complexTrailingRejected_refuted,

  proven "docssyntaxcov-toml-lexer-char" "base/toml/parser.jl" ["next_char", "eat_char", "peek"]
    "TOML character movement preserves state and updates indices, lines and columns."
    "base/toml/parser.jl:413-433" ``TomlLex.NextCharSpec ``TomlLex.nextCharSpec,
  proven "docssyntaxcov-toml-lexer-accept" "base/toml/parser.jl" ["accept", "accept_batch", "accept_n"]
    "TOML acceptance consumes exactly the accepted lookahead run."
    "base/toml/parser.jl:437-467" ``TomlLex.AcceptBatchSpec ``TomlLex.acceptBatchSpec,
  proven "docssyntaxcov-toml-lexer-accept-one" "base/toml/parser.jl" ["accept"]
    "accept eats only an accepted non-EOF lookahead."
    "base/toml/parser.jl:437-448" ``TomlLex.AcceptSpec ``TomlLex.acceptSpec,
  proven "docssyntaxcov-toml-lexer-accept-n" "base/toml/parser.jl" ["accept_n"]
    "accept_n mirrors its recursive count."
    "base/toml/parser.jl:460-467" ``TomlLex.AcceptNSpec ``TomlLex.acceptNSpec,
  proven "docssyntaxcov-toml-whitespace" "base/toml/parser.jl"
    ["iswhitespace", "isnewline", "skip_ws", "skip_ws_nl_no_comment"]
    "Whitespace predicates and skippers stop on the first nonmatching lookahead."
    "base/toml/parser.jl:469-474" ``TomlLex.SkipWsSpec ``TomlLex.skipWsSpec,
  proven "docssyntaxcov-toml-comments" "base/toml/parser.jl"
    ["skip_comment", "skip_ws_nl", "skip_ws_nl_toplevel", "skip_ws_comment"]
    "Comment skipping consumes comments and queues captured text."
    "base/toml/parser.jl:476-544" ``TomlLex.SkipCommentSpec ``TomlLex.skipCommentSpec,
  proven "docssyntaxcov-toml-comment-state" "base/toml/parser.jl"
    ["flush_pending_comments!", "attach_pending_comments!", "attach_inline_comment!"]
    "Captured comments move to floating, above and inline containers."
    "base/toml/parser.jl:546-571" ``TomlLex.AttachSpec ``TomlLex.attachSpec,
  proven "docssyntaxcov-toml-path-marker" "base/toml/parser.jl"
    ["path_traverses_array", "set_marker!", "take_substring"]
    "Path traversal detects arrays and marker slicing uses the recorded prior position."
    "base/toml/parser.jl:573-585" ``TomlLex.PathTraversesArraySpec ``TomlLex.pathTraversesArraySpec,
  proven "docssyntaxcov-toml-containers" "base/toml/parser.jl"
    ["CommentBlock", "Comments", "isempty", "empty!", "=="]
    "Comment containers construct, clear and compare their fields."
    "base/toml/parser.jl:45-69" ``TomlLex.CommentContainers ``TomlLex.commentContainers,
  proven "docssyntaxcov-toml-parser-construction" "base/toml/parser.jl" ["Parser", "startup", "reinit!"]
    "Parser constructors and reinit establish the same fresh state."
    "base/toml/parser.jl:136-209" ``TomlLex.ParserConstruction ``TomlLex.parserConstruction,
  proven "docssyntaxcov-toml-try-macro" "base/toml/parser.jl" ["@try"]
    "@try returns ParserError values and otherwise yields the result."
    "base/toml/parser.jl:219-225" ``TomlLex.TryMacro ``TomlLex.tryMacroSpec,
  proven "docssyntaxcov-toml-errors" "base/toml/parser.jl"
    ["ParserError", "format_error_message_for_err_type", "point_to_line", "showerror"]
    "Parser errors construct and format their message, location and caret line."
    "base/toml/parser.jl:340-406" ``TomlLex.FormatErrorSpec ``TomlLex.formatErrorSpec,
  proven "docssyntaxcov-toml-datetime-copy" "base/toml/parser.jl" ["DateTime", "copyto_typed!"]
    "DateTime composes Date and Time and typed copying preserves length and prefix."
    "base/toml/parser.jl:23-24,879-884" ``TomlLex.CopytoTypedSpec ``TomlLex.copytoTypedSpec,

  proven "docssyntaxcov-toml-print-escaped" "base/toml/printer.jl" ["print_toml_escaped"]
    "Escaped TOML output contains only valid bytes."
    "base/toml/printer.jl:7-33" ``TomlPrint.EscapedBytesValid ``TomlPrint.escapedBytesValid,
  proven "docssyntaxcov-toml-print-validity" "base/toml/printer.jl"
    ["is_valid_toml_value", "_is_valid_toml_value", "to_toml_value"]
    "TOML value validation and conversion follow the supported value types."
    "base/toml/printer.jl:38-43,66-75" ``TomlPrint.ValidityAndConversion ``TomlPrint.validityAndConversion,
  proven "docssyntaxcov-toml-print-key" "base/toml/printer.jl" ["printkey"]
    "TOML keys use bare form when valid and quoted escaped form otherwise."
    "base/toml/printer.jl:49-64" ``TomlPrint.PrintkeyForms ``TomlPrint.printkeyForms,
  proven "docssyntaxcov-toml-print-value" "base/toml/printer.jl" ["printvalue", "print_inline_table"]
    "TOML scalar, string, array and inline-table values use their specified syntax."
    "base/toml/printer.jl:82-173" ``TomlPrint.PrintvalueForms ``TomlPrint.printvalueForms,
  proven "docssyntaxcov-toml-print-comments" "base/toml/printer.jl"
    ["print_comment_line", "print_comments_above", "print_comment_inline", "has_comments", "print_comments_floating"]
    "Comment output is sanitized and attached only to its recorded path."
    "base/toml/printer.jl:182-225,252-259" ``TomlPrint.CommentSanitized ``TomlPrint.commentSanitized,
  proven "docssyntaxcov-toml-print-hoisted" "base/toml/printer.jl" ["print_hoisted_inline_comments"]
    "Hoisted inline comments traverse sorted or insertion-order table keys recursively."
    "base/toml/printer.jl:228-250" ``TomlPrint.HoistedCommentsBehavior ``TomlPrint.hoistedCommentsBehavior,
  proven "docssyntaxcov-toml-print-tabular" "base/toml/printer.jl" ["is_table", "is_array_of_tables", "is_tabular"]
    "Tabular predicates recognize dictionaries and nonempty arrays of dictionaries."
    "base/toml/printer.jl:265-270" ``TomlPrint.TabularPredicates ``TomlPrint.tabularPredicates,
  proven "docssyntaxcov-toml-print-table" "base/toml/printer.jl" ["print_table"]
    "Scalar tables produce one valid key-value line per entry."
    "base/toml/printer.jl:272-379" ``TomlPrint.ScalarTableLines ``TomlPrint.scalarTableLines,
  proven "docssyntaxcov-toml-print-api" "base/toml/printer.jl" ["print"]
    "All four print overloads delegate to root print_table with the requested conversion."
    "base/toml/printer.jl:386-393" ``TomlPrint.PrintApi ``TomlPrint.printApi,
  refuted "docssyntaxcov-toml-print-inline-array-table" "base/toml/printer.jl" ["print_table", "print"]
    "Every TOML.print result parses as TOML."
    "stdlib/TOML/src/TOML.jl print docstring"
    "none found (queries: TOML print, TOML print inline_tables, TOML print array of tables inline)"
    "An inline-marked element in an array of tables prints as a bare inline table after [[a]]."
    ``TomlPrint.InlineArrayTableValid ``TomlPrint.inlineArrayTableValid_refuted,
  refuted "docssyntaxcov-toml-print-by-inline" "base/toml/printer.jl"
    ["print_inline_table", "print_hoisted_inline_comments", "print"]
    "sorted=true applies the by function to inline tables."
    "stdlib/TOML/src/TOML.jl print docstring"
    "#46385 (closed, related); queries: TOML print sorted by, TOML inline table"
    "Inline tables use plain key sorting and ignore by."
    ``TomlPrint.InlineSortedBy ``TomlPrint.inlineSortedBy_refuted,

  proven "docssyntaxcov-linking-env" "base/linking.jl" ["adjust_ENV!"]
    "Environment adjustment prepends the selected PATH and library path variables."
    "base/linking.jl:25-42" ``Linking.AdjustEnvForms ``Linking.adjustEnvForms,
  proven "docssyntaxcov-linking-tools" "base/linking.jl" ["PATH", "lld", "dsymutil"]
    "Bundled linker tools are preferred and commands receive the adjusted environment."
    "base/linking.jl:44-89" ``Linking.ToolPaths ``Linking.toolPaths,
  proven "docssyntaxcov-linking-ld" "base/linking.jl" ["ld"]
    "ld selects the platform flavor and strict-definition arguments."
    "base/linking.jl:91-128" ``Linking.LdForms ``Linking.ldForms,
  proven "docssyntaxcov-linking-whole-archive" "base/linking.jl" ["whole_archive", "cc_arg"]
    "whole_archive uses force_load on macOS and paired flags elsewhere."
    "base/linking.jl:143-151" ``Linking.WholeArchiveForms ``Linking.wholeArchiveForms,
  proven "docssyntaxcov-linking-dirs" "base/linking.jl"
    ["libdir", "private_libdir", "shlibdir", "verbose_linking", "_find_static", "_find_loaded"]
    "Library directories, verbosity and static/loaded lookup follow installation state."
    "base/linking.jl:159-182" ``Linking.LibraryDirForms ``Linking.libraryDirForms,
  proven "docssyntaxcov-linking-image" "base/linking.jl" ["link_image_cmd", "link_image"]
    "Image linking composes the platform command and link_image executes it."
    "base/linking.jl:184-233" ``Linking.LinkImageCmdShape ``Linking.linkImageCmdShape,
  proven "docssyntaxcov-linking-is-library" "base/linking.jl" ["is_library_file"]
    "Library-file matching supports exact, suffix-version and wildcard forms."
    "base/linking.jl:251-267" ``Linking.IsLibraryFileForms ``Linking.isLibraryFileForms,
  proven "docssyntaxcov-linking-library-files" "base/linking.jl"
    ["library_listings", "library_files!", "library_files"]
    "Library discovery scans each directory once and stops at the first containing matches."
    "base/linking.jl:270-304" ``Linking.LibraryFilesForms ``Linking.libraryFilesForms,
  refuted "docssyntaxcov-library-files-unrelated-invalid" "base/linking.jl"
    ["is_library_file", "library_files!"]
    "Unrelated directory entries do not make library_files! throw."
    "base/linking.jl:288-295"
    "none found (queries: library_files invalid version unrelated file, is_library_file parse_dl_name_version)"
    "An unrelated four-part soversion reaches the unguarded fallback parser and aborts discovery."
    ``Linking.LibraryFilesNoThrow ``Linking.libraryFilesNoThrow_refuted,
  proven "docssyntaxcov-linking-runtime" "base/linking.jl"
    ["runtime_library_names", "runtime_libraries", "resolve_libraries"]
    "Runtime-library names validate components and resolution includes every required library."
    "base/linking.jl:306-363" ``Linking.RuntimeLibraries ``Linking.runtimeLibraries_spec,

  proven "docssyntaxcov-syntax-constructors" "base/syntax.jl" ["Syntax", "SyntaxContext"]
    "Syntax constructors store the supplied fields and documented defaults."
    "base/syntax.jl:57-80" ``Syntax.SyntaxConstructors ``Syntax.syntaxConstructors,
  proven "docssyntaxcov-syntax-accessors" "base/syntax.jl"
    ["head", "is_leaf", "numchildren", "children", "getindex", "firstindex", "lastindex"]
    "Syntax accessors expose the head and child sequence with one-based indexing."
    "base/syntax.jl:82-109" ``Syntax.SyntaxAccessors ``Syntax.syntaxAccessors,
  proven "docssyntaxcov-syntax-node-string" "base/syntax.jl" ["node_string"]
    "Fallback node rendering follows depth, value and child branches."
    "base/syntax.jl:115-142" ``Syntax.NodeStringBehavior ``Syntax.nodeStringBehavior,
  proven "docssyntaxcov-syntax-validation" "base/syntax.jl"
    ["assert_syntax", "_assert_syntax_node", "_assert_syntax", "_debug_check_attrs", "setproperty!"]
    "Syntax validation enforces leaf kinds, values, child kinds and acyclicity."
    "base/syntax.jl:147-231,287-293" ``Syntax.SyntaxValidation ``Syntax.syntaxValidation,
  proven "docssyntaxcov-syntax-mknode" "base/syntax.jl" ["@mknode"]
    "@mknode copies fields, applies attributes and records provenance and macro source."
    "base/syntax.jl:247-285" ``Syntax.MknodeBehavior ``Syntax.mknodeBehavior,
  proven "docssyntaxcov-syntax-mapchildren" "base/syntax.jl" ["mapchildren"]
    "mapchildren returns the original node when unchanged and allocates at the first change."
    "base/syntax.jl:296-320" ``Syntax.MapchildrenBehavior ``Syntax.mapchildrenBehavior,
  proven "docssyntaxcov-syntax-context" "base/syntax.jl"
    ["is_base_layer", "base_layer", "escape_layer", "syntax_module", "syntax_name", "edition", "_with_context"]
    "Layer and context helpers follow escape chains, module overrides and edition defaults."
    "base/syntax.jl:325-355" ``Syntax.ContextLayers ``Syntax.contextLayers,
  proven "docssyntaxcov-syntax-scope" "base/syntax.jl"
    ["adopt_scope", "fill_context", "remove_scope", "_trim_provenance", "trim_provenance"]
    "Scope transformations update contexts recursively and preserve terminal source references."
    "base/syntax.jl:359-437" ``Syntax.ScopeTransforms ``Syntax.scopeTransforms,
  proven "docssyntaxcov-syntax-scope-show" "base/syntax.jl" ["show(::ScopeLayer)", "show(::SyntaxContext)"]
    "ScopeLayer and SyntaxContext displays expose escape, edition, internal and macro context."
    "base/syntax.jl:439-469" ``Syntax.ScopeDisplay ``Syntax.scopeDisplay,
  proven "docssyntaxcov-syntax-provenance" "base/syntax.jl"
    ["provenance", "prov", "prov_end", "sourceref", "macro_prov", "macro_prov_end", "unexpanded_sourceref", "flattened_provenance", "_flattened_provenance"]
    "Provenance helpers traverse source and macro chains in documented order."
    "base/syntax.jl:489-568" ``Syntax.ProvenanceBehavior ``Syntax.provenanceBehavior,
  proven "docssyntaxcov-syntax-source" "base/syntax.jl"
    ["filename", "source_line", "first_linenode"]
    "Source locations derive filenames and line numbers from terminal text references."
    "base/syntax.jl:572-584" ``Syntax.SourceLocationBehavior ``Syntax.sourceLocationBehavior,
  proven "docssyntaxcov-syntax-expr-lines" "base/syntax.jl"
    ["_first_linenode", "first_linenode(::Expr)", "_unescape_lnn", "_get_inner_lnn"]
    "Expr line-node helpers find, unwrap and select the applicable source line."
    "base/syntax.jl:597-634" ``Syntax.ExprLineBehavior ``Syntax.exprLineBehavior,
  proven "docssyntaxcov-syntax-expr-to-syntax" "base/syntax.jl"
    ["isa_lowering_ast_node", "expr_to_syntax", "_expr_to_syntax"]
    "Expr-to-Syntax conversion preserves identifiers, quotes, children and source state."
    "base/syntax.jl:639-699" ``Syntax.ExprSyntaxBehavior ``Syntax.exprSyntaxBehavior,
  proven "docssyntaxcov-syntax-meta-call" "base/syntax.jl" ["_is_meta_doc_block", "is_eventually_call"]
    "Meta-doc blocks and nested call signatures are recognized by their exact shapes."
    "base/syntax.jl:702-713" ``Syntax.MetaCallBehavior ``Syntax.metaCallBehavior,
  proven "docssyntaxcov-syntax-to-expr" "base/syntax.jl" ["syntax_to_expr", "push_lno!"]
    "Syntax-to-Expr conversion restores identifiers, values, quotes, children and line nodes."
    "base/syntax.jl:718-788" ``Syntax.SyntaxExprBehavior ``Syntax.syntaxExprBehavior,
  proven "docssyntaxcov-syntax-parser-eval" "base/syntax.jl" ["_c_parseall_expr", "fl_toplevel_eval"]
    "Parser and top-level-eval wrappers preserve arguments and offsets."
    "base/syntax.jl:791-807" ``Syntax.ParserEvalWrappers ``Syntax.parserEvalWrappers,
  proven "docssyntaxcov-syntax-print-helpers" "base/syntax.jl" ["attrsummary", "subscript_str", "_value_string"]
    "Printing helpers render attributes, subscript digits and leaf kinds."
    "base/syntax.jl:812-863" ``Syntax.PrintingHelpers ``Syntax.printingHelpers,
  proven "docssyntaxcov-syntax-tree-show" "base/syntax.jl" ["_show_syntax_tree", "show(::Syntax)", "_show_syntax_tree_sexpr"]
    "Tree displays validate the node and recurse through every child."
    "base/syntax.jl:865-920" ``Syntax.SyntaxTreePrinting ``Syntax.syntaxTreePrinting,

  proven "docssyntaxcov-binary-tagvalue" "base/binaryplatforms.jl" ["tagvalue"]
    "Tag values preserve strings and convert symbols and abstract strings to String."
    "base/binaryplatforms.jl:112-114" ``Binary.TagvalueMethods ``Binary.tagvalueMethods,
  proven "docssyntaxcov-binary-dict" "base/binaryplatforms.jl" ["tags", "getindex", "haskey", "setindex!"]
    "Platform dictionary operations delegate to normalized tags and return the platform on mutation."
    "base/binaryplatforms.jl:174-182" ``Binary.PlatformDictMethods ``Binary.platformDictMethods,
  proven "docssyntaxcov-binary-hash-show" "base/binaryplatforms.jl" ["hash", "==", "show"]
    "Hashing includes tags and strategies, equality compares both, and displays use sorted extra tags."
    "base/binaryplatforms.jl:185-220" ``Binary.HashEqShowMethods ``Binary.hashEqShowMethods,
  proven "docssyntaxcov-binary-validation-helpers" "base/binaryplatforms.jl"
    ["throw_invalid_key", "throw_os_mismatch", "throw_libc_mismatch", "throw_call_abi_mismatch", "throw_version_number"]
    "Nested validation helpers throw ArgumentError for their rejected condition."
    "base/binaryplatforms.jl:223-291" ``Binary.ValidationHelpers ``Binary.validationHelpers,
  proven "docssyntaxcov-binary-add-platform-tag" "base/binaryplatforms.jl" ["add_platform_tag!"]
    "Platform tag insertion lowercases names, applies compatibility aliases and normalizes versions."
    "base/binaryplatforms.jl:116-151" ``Binary.AddPlatformTagBehavior ``Binary.addPlatformTagBehavior,
  proven "docssyntaxcov-binary-compare-strategy" "base/binaryplatforms.jl"
    ["set_compare_strategy!", "get_compare_strategy", "compare_default"]
    "Comparison strategies require an existing key, store the function and default to equality."
    "base/binaryplatforms.jl:295-323" ``Binary.CompareStrategyMethods ``Binary.compareStrategyMethods,
  proven "docssyntaxcov-binary-host-accessors" "base/binaryplatforms.jl"
    ["HostPlatform", "os", "platform_name", "cxxstring_abi", "wordsize"]
    "Host conversion installs version caps and accessors return normalized platform attributes."
    "base/binaryplatforms.jl:370-546" ``Binary.HostAccessorMethods ``Binary.hostAccessorMethods,
  proven "docssyntaxcov-binary-strings" "base/binaryplatforms.jl"
    ["cxxstring_abi", "call_abi_str", "libc_str", "platform_dlext"]
    "Platform ABI strings and dynamic-library extensions follow OS and tag values."
    "base/binaryplatforms.jl:520-520,632-657,847-855" ``Binary.PlatformStringMethods ``Binary.platformStringMethods,
  proven "docssyntaxcov-binary-system" "base/binaryplatforms.jl" ["Sys.isapple", "Sys.islinux", "Sys.iswindows", "Sys.isfreebsd", "Sys.isopenbsd", "Sys.isbsd", "Sys.isunix"]
    "Platform system predicates agree with the os tag."
    "base/binaryplatforms.jl:651-657" ``Binary.SystemPredicates ``Binary.systemPredicates,
  proven "docssyntaxcov-binary-mapping-parse" "base/binaryplatforms.jl"
    ["get_set", "c", "parse(::Platform)", "tryparse(::Platform)"]
    "Mapping helpers build named regex alternatives and parsing wrappers preserve conversion and failure."
    "base/binaryplatforms.jl:671-838" ``Binary.MappingParseHelpers ``Binary.mappingParseHelpers,
  proven "docssyntaxcov-binary-dl-helpers" "base/binaryplatforms.jl"
    ["_this_os_name", "parse_dl_name_version(::AbstractString)", "get_csl_member", "_get_libgfortran_path", "_get_libstdcxx_handle", "detect_libgfortran_version"]
    "Dynamic-library helpers choose OS regexes and inspect loaded compiler-support libraries."
    "base/binaryplatforms.jl:858-1004" ``Binary.DynamicLibraryHelpers ``Binary.dynamicLibraryHelpers,
  proven "docssyntaxcov-binary-cxx-host" "base/binaryplatforms.jl"
    ["open_libllvm", "detect_cxxstring_abi", "host_triplet", "HostPlatform()"]
    "C++ ABI detection closes opened LLVM handles and host triplets append detected and build tags."
    "base/binaryplatforms.jl:1038-1126" ``Binary.CxxHostMethods ``Binary.cxxHostMethods,
  proven "docssyntaxcov-binary-match-adapters" "base/binaryplatforms.jl"
    ["platforms_match(::String)", "platforms_match(::AbstractString)", "match_loss"]
    "String adapters parse before matching and match_loss is the union-minus-intersection tag count."
    "base/binaryplatforms.jl:1190-1230" ``Binary.MatchAdapters ``Binary.matchAdapters,

  proven "docssyntaxcov-toml-eat-char" "base/toml/parser.jl" ["eat_char"]
    "eat_char returns the lookahead and replaces it with next_char."
    "base/toml/parser.jl:427-431" ``TomlLex.EatCharSpec ``TomlLex.eatCharSpec,
  proven "docssyntaxcov-toml-peek" "base/toml/parser.jl" ["peek"]
    "peek returns the current lookahead without changing the parser."
    "base/toml/parser.jl:433" ``TomlLex.PeekSpec ``TomlLex.peekSpec,
  proven "docssyntaxcov-toml-whitespace-predicates" "base/toml/parser.jl" ["iswhitespace", "isnewline"]
    "TOML whitespace is space or tab and newline is LF or CR."
    "base/toml/parser.jl:469-470" ``TomlLex.WsNlSpec ``TomlLex.wsNlSpec,
  proven "docssyntaxcov-toml-skip-wsnl" "base/toml/parser.jl" ["skip_ws_nl"]
    "skip_ws_nl mirrors one whitespace and comment iteration before stopping or recurring."
    "base/toml/parser.jl:476-490" ``TomlLex.SkipWsNlSpec ``TomlLex.skipWsNlSpec,
  proven "docssyntaxcov-toml-skip-ws-comment" "base/toml/parser.jl" ["skip_ws_comment"]
    "skip_ws_comment runs skip_ws followed by skip_comment."
    "base/toml/parser.jl:541-544" ``TomlLex.SkipWsCommentSpec ``TomlLex.skipWsCommentSpec,
  proven "docssyntaxcov-toml-flush-comments" "base/toml/parser.jl" ["flush_pending_comments!"]
    "Flushing comments moves the pending queue to the active table and clears it."
    "base/toml/parser.jl:546-555" ``TomlLex.FlushSpec ``TomlLex.flushSpec,
  proven "docssyntaxcov-toml-toplevel-comments" "base/toml/parser.jl" ["skip_ws_nl_toplevel"]
    "Top-level whitespace skipping selects its capture or no-capture loop."
    "base/toml/parser.jl:493-524" ``TomlLex.ToplevelSpec ``TomlLex.toplevelSpec,
  proven "docssyntaxcov-toml-marker" "base/toml/parser.jl" ["set_marker!", "take_substring"]
    "The marker records prevpos and take_substring slices through the byte before lookahead."
    "base/toml/parser.jl:584-585" ``TomlLex.MarkerSpec ``TomlLex.markerSpec,
  proven "docssyntaxcov-toml-error-constructors" "base/toml/parser.jl" ["ParserError"]
    "ParserError constructors leave source locations unset."
    "base/toml/parser.jl:340-341" ``TomlLex.ParserErrorCtors ``TomlLex.parserErrorCtors,
  proven "docssyntaxcov-toml-point-line" "base/toml/parser.jl" ["point_to_line"]
    "point_to_line rejects reversed intervals and runs the caret-line traversal after index normalization."
    "base/toml/parser.jl:365-385" ``TomlLex.PointToLineSpec ``TomlLex.pointToLineSpec,
  proven "docssyntaxcov-toml-showerror" "base/toml/parser.jl" ["showerror"]
    "showerror composes the message, location, source line and marker line."
    "base/toml/parser.jl:387-406" ``TomlLex.ShowerrorSpec ``TomlLex.showerrorSpec,
  proven "docssyntaxcov-toml-datetime-constructor" "base/toml/parser.jl" ["DateTime"]
    "The seven-argument DateTime constructor composes Date and Time."
    "base/toml/parser.jl:23-24" ``TomlLex.DateTimeCtor ``TomlLex.dateTimeCtor,
  proven "docssyntaxcov-toml-value-methods" "base/toml/parser.jl"
    ["parse_toplevel", "parse_key", "parse_value", "parse_inline_table", "parse_inf", "parse_nan", "parse_bool", "isvalid_hex", "isvalid_oct", "isvalid_binary", "accept_batch_underscore", "take_string_or_substring", "parse_integer", "parse_hex", "parse_oct", "parse_bin", "ok_end_value"]
    "TOML value helpers terminate with a value or explicit exception, and character predicates match their bodies."
    "base/toml/parser.jl:620-642,807-1170" ``TomlRows.ValueMethodTotality ``TomlRows.valueMethodTotality,
  proven "docssyntaxcov-toml-date-methods" "base/toml/parser.jl"
    ["accept_two", "try_return_datetime", "try_return_date", "try_return_time", "_parse_local_time", "parse_local_time", "parse_datetime"]
    "TOML date and time helpers terminate with a value or explicit parser exception."
    "base/toml/parser.jl:1197-1353" ``TomlRows.DateMethodTotality ``TomlRows.dateMethodTotality,
  proven "docssyntaxcov-toml-string-methods" "base/toml/parser.jl"
    ["parse_string_start", "parse_string_continue", "take_chunks", "stop_candidates_multiline", "stop_candidates_singleline", "stop_candidates_multiline_quoted", "stop_candidates_singleline_quoted"]
    "TOML string helpers terminate with a string or explicit exception, and stop predicates match their delimiters."
    "base/toml/parser.jl:1360-1462" ``TomlRows.StringMethodTotality ``TomlRows.stringMethodTotality,
  proven "docssyntaxcov-binary-direct-parse" "base/binaryplatforms.jl"
    ["get_field", "split_tags", "extract_os_version", "VNorNothing", "libgfortran_version", "libstdcxx_version", "os_str", "parse(::Platform)"]
    "BinaryPlatforms parsing and version access helpers return a result or explicit exception on every input."
    "base/binaryplatforms.jl:481-487,495-513,605-629,760-825" ``Binary.DirectParseMethods ``Binary.directParseMethods,
  proven "docssyntaxcov-syntax-layer-totality" "base/syntax.jl" ["base_layer", "escape_layer"]
    "Layer traversal and escaping terminate with a layer/context or explicit exception."
    "base/syntax.jl:330-341" ``Syntax.LayerMethodTotality ``Syntax.layerMethodTotality
]

end JuliaLean.DocsSyntaxCov
