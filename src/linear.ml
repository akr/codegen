open Pp
open Term
open EConstr

let linear_type_list_empty : t list = []

let linear_type_list = Summary.ref linear_type_list_empty ~name:"CodeGenLinearTypeList"

let register_linear_type (ty : Constrexpr.constr_expr) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (ty2, euc) = Constrintern.interp_constr env sigma ty in
  let ty3 = EConstr.of_constr ty2 in
  linear_type_list := ty3 :: !linear_type_list;
  Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty3);
