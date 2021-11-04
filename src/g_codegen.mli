val __coq_plugin_name : string
val wit_ind_cstr_caselabel_accessors :
  (Names.Id.t * string * string list, unit, unit) Genarg.genarg_type
val ind_cstr_caselabel_accessors :
  (Names.Id.t * string * string list) Pcoq.Entry.t
val wit_s_or_d : (State.s_or_d, unit, unit) Genarg.genarg_type
val s_or_d : State.s_or_d Pcoq.Entry.t
val wit_id_or_underscore : (Names.Id.t option, unit, unit) Genarg.genarg_type
val id_or_underscore : Names.Id.t option Pcoq.Entry.t
val wit_string_or_qualid :
  (State.string_or_qualid, unit, unit) Genarg.genarg_type
val string_or_qualid : State.string_or_qualid Pcoq.Entry.t
val wit_constr_or_underscore :
  (Constrexpr.constr_expr option, unit, unit) Genarg.genarg_type
val constr_or_underscore : Constrexpr.constr_expr option Pcoq.Entry.t
val wit_sp_instance_names3 :
  (State.sp_instance_names, unit, unit) Genarg.genarg_type
val sp_instance_names3 : State.sp_instance_names Pcoq.Entry.t
val wit_sp_instance_names2 :
  (State.sp_instance_names, unit, unit) Genarg.genarg_type
val sp_instance_names2 : State.sp_instance_names Pcoq.Entry.t
val wit_ind_constructor :
  (State.ind_constructor, unit, unit) Genarg.genarg_type
val ind_constructor : State.ind_constructor Pcoq.Entry.t
val wit_string_or_none : (string option, unit, unit) Genarg.genarg_type
val string_or_none : string option Pcoq.Entry.t
val wit_genflag : (State.genflag, unit, unit) Genarg.genarg_type
val genflag : State.genflag Pcoq.Entry.t
