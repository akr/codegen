type indimp_mods = {
  indimp_mods_output_type : (string * string) option;
  indimp_mods_output_impl : (string * string) option;
  indimp_mods_prefix : string option;
}

val indimp_mods_empty : indimp_mods
val merge_indimp_mods : indimp_mods -> indimp_mods -> indimp_mods

val command_indimp : ?force_imm:bool -> ?force_heap:bool -> Constrexpr.constr_expr -> indimp_mods -> unit
