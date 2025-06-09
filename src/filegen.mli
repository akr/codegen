open State

val defined_sections : string list
val codegen_add_source_generation : code_generation -> unit
val codegen_add_header_generation : code_generation -> unit
val check_section : string -> unit
