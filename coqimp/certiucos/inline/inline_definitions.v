Require Import include_frm.

Definition inline_function_code := (list expr) -> stmts.
Definition inline_function_asrt := (asrt ) -> (list logicvar) -> (list expr) -> asrt.
Definition make_inl_proof (code: inline_function_code) (pre post: inline_function_asrt) :=
  forall lexpr a b I e d o ll li tid,
    (o ==> EX lg : list logicvar, p_local li tid lg ** Atrue ) ->
    {|a, b, li, I, e, d|} |- tid {{o ** (pre o ll lexpr)}} code lexpr {{o ** (post o ll lexpr)}}.

Record Inline_record :=
  Inline_record_cons
    {
    inl_code : inline_function_code;
    inl_pre  : inline_function_asrt;
    inl_post : inline_function_asrt;
    inl_proof: make_inl_proof inl_code inl_pre inl_post
  }. 

Definition inline_call inline_function_record lexpr :=
  (inl_code inline_function_record) lexpr.

