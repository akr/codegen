open State

val defined_sections : string list
val codegen_add_generation : string -> string -> code_generation -> unit
val codegen_add_source_generation : string -> code_generation -> unit
val codegen_add_header_generation : string -> code_generation -> unit

