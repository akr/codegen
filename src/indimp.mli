type indimp_mods = {
  indimp_mods_heap : bool option;
  indimp_mods_output_type : (string * string) option;
  indimp_mods_output_prototype : (string * string) option;
  indimp_mods_output_impl : (string * string) option;
  indimp_mods_prefix : string option;
  indimp_mods_static : bool option;
}

val indimp_mods_empty : indimp_mods
val merge_indimp_mods : indimp_mods -> indimp_mods -> indimp_mods

val command_indimp : Constrexpr.constr_expr -> indimp_mods -> unit
