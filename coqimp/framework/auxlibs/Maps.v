Set Implicit Arguments.
Unset Strict Implicit.

(** permission map class **)
Class PermMap (A B T:Type) :=
  {
    usePerm : bool;
    (** indicate whether to use Permission **)
    
    isRw : B -> bool;
    (** true: have write permission; false: have read permission **)
    flip : B -> B;
    (** flip permission: turn RO to RW, or RW to RO.
        Or Return None if all permission are RW **)
    sameV : B -> B -> Prop;
    (** [sameV v1 v2] means v1 v2 are same except for their permissions **)
    same : B -> B -> bool;
    (** [same v1 v2 = true ] means v1 = v2 **)
    emp: T;
    get : T -> A -> option B;
    set : T -> A -> B -> T;
    del : T -> A -> T;
    sig : A -> B -> T;
    join : T -> T -> T -> Prop;
    merge: T -> T -> T;
    minus: T -> T -> T;
    (** I only deal with emp, get, set, sig, join, merge at present  **)

    map_dec_a:
      forall (t1 t2: A), {t1 = t2} + {t1 <> t2};

    map_same:
      forall (v1 v2: B),
        usePerm = true ->
        same v1 v2 = true ->
        v1 = v2;

    map_same':
      forall (v1 v2: B),
        usePerm = true ->
        same v1 v2 = false ->
        v1 <> v2;
    
    (** * join **)
    map_join_emp:
      forall x, join x emp x;

    map_join_pos:
      forall x y,
        join x y emp ->
        x = emp /\ y = emp;

    map_join_comm:
      forall x y z,
        join x y z ->
        join y x z;

    map_join_assoc:
      forall a b mab c mabc,
        join a b mab ->
        join mab c mabc ->
        exists mbc,
          join a mbc mabc /\
          join b c mbc;

    map_join_cancel:
      forall a b b' c,
        join a b c ->
        join a b' c ->
        b = b';

    map_join_deter:
      forall a b c c',
        join a b c ->
        join a b c' ->
        c = c';

    (** * saveV and flip: Permission specific **)
    map_sv_ref:
      forall v, usePerm = true -> sameV v v;
    
    map_sv_comm:
      forall v v',
        usePerm = true ->
        sameV v v' ->
        sameV v' v;

    map_sv_assoc:
      forall v1 v2 v3,
        usePerm = true ->
        sameV v1 v2 ->
        sameV v2 v3 ->
        sameV v1 v3;

    map_perm_eql:
      forall v1 v2,
        usePerm = true ->
        sameV v1 v2 ->
        isRw v1 = isRw v2 ->
        v1 = v2;
 
    map_flip_isRw:
      forall v,
        usePerm = true ->
        isRw (flip v) = negb (isRw v);

    map_flip_sv:
      forall v,
        usePerm = true ->
        sameV v (flip v);
    
    (** * get **)
    (** ** general **)
    map_emp_get:
      forall t, get emp t = None;

    map_eql:
      forall x y,
        (forall t, get x t = get y t) ->
        x = y;

    map_disjoint:
      forall x y,
        (forall t, get x t = None \/
              get y t = None \/
              (exists v,
                  usePerm = true /\
                  get x t = Some v /\
                  get y t = Some v /\
                  isRw v = false)) ->
        exists z, join x y z;
    
    map_get_unique:
      forall x t v v',
        get x t = Some v ->
        get x t = Some v' ->
        v = v';
    (** above two axiom describe T to be a set of (A, B) **)

    map_get_sig:
      forall t v,
        get (sig t v) t = Some v;

    map_get_sig':
      forall t t' v,
        t <> t' ->
        get (sig t v) t' = None;
    
    map_get_set:
      forall x t v,
        get (set x t v) t = Some v;

    map_get_set':
      forall x t t' v,
        t <> t' ->
        get (set x t v) t' = get x t'; 

    map_join_get_none:
      forall x y z t,
        join x y z ->
        get x t = None ->
        get z t = get y t;

    (** ** no permission **)
    map_join_get_some:
      forall x y z t v1 v2,
        usePerm = false ->
        join x y z ->
        get x t = Some v1 ->
        get y t = Some v2 ->
        False;

    (** ** use permission **)
    map_join_getp_some:
      forall x y z t v1 v2 v',
        usePerm = true ->
        join x y z ->
        get x t = Some v1 ->
        get y t = Some v2 ->
        v' = flip v1 ->
        v1 = v2 /\ isRw v1 = false /\ get z t = Some v';
    
    (** * set **)
    (** ** general **)
    map_set_emp:
      forall t v,
        set emp t v = sig t v; 

    map_set_sig:
      forall t v v',
        set (sig t v) t v' = sig t v';

    map_join_set_none:
      forall x y z t v',
        join x y z ->
        get y t = None ->
        join (set x t v') y (set z t v');

    (** ** use permission **)
    map_join_set_perm:
      forall x y z t v v',
        usePerm = true ->
        join x y z ->
        get x t = None ->
        get y t = Some v ->
        isRw v = false ->
        v' = flip v ->
        join (set x t v) y (set z t v');
    
    (** * sig **)
    (** ** general **)
    map_join_get_sig:
      forall x t v,
        get x t = Some v ->
        exists x', join (sig t v) x' x;

    (** ** use permission **)
    map_join_get_sig_perm:
      forall x t v v',
        usePerm = true ->
        get x t = Some v ->
        isRw v = true ->
        v' = flip v ->
        exists x1 x2, join (sig t v') x1 x /\ join (sig t v') x2 x1;
        
    
    (** * merge **)
    map_merge_sem:
      (** def1 **)
      forall m1 m2 a,
        usePerm = false ->
        get (merge m1 m2) a 
        = match (get m1 a, get m2 a) with
            | (Some b1, Some b2) => Some b1
            | (Some b1, None) => Some b1
            | (None, Some b2) => Some b2
            | (None, None) => None
          end;

    map_merge_semp:
      (** def2 **)
      forall m1 m2 a,
        usePerm = true ->
        get (merge m1 m2) a
        = match (get m1 a, get m2 a) with
            | (Some b1, Some b2) => 
              match (same b1 b2) return (option B) with
                | true => match (isRw b1) with
                             | true => Some b1
                             | false => Some (flip b1)
                           end
                | false => Some b1
              end
            | (None, Some b2) => Some b2
            | (Some b1, None) => Some b1
            | (None, None) => None
          end;
    
    map_join_merge:
      (** the scope of exists is very large, using parenthesis **)
      forall x y,
        (exists z, join x y z) ->
        join x y (merge x y);

    map_merge_comm:
      forall x y,
        (exists z, join x y z) ->
        merge x y = merge y x;

    (** * disjoint **)
    map_disjoint_semp:
      forall m1 m2,
        usePerm = true ->
        (forall t,
            match (get m1 t, get m2 t) with
              | (Some b0, Some b1) => b0 = b1 /\ isRw b0 = false
              | (Some b0, None) => True
              | (None, Some b1) => True
              | (None, None) => True
            end) ->
        (exists m, join m1 m2 m);

    map_disjoint_semp':
      forall m1 m2,
        usePerm = true ->
        (exists m, join m1 m2 m) ->
        (forall t,
            match (get m1 t, get m2 t) with
              | (Some b0, Some b1) => b0 = b1 /\ isRw b0 = false
              | (Some b0, None) => True
              | (None, Some b1) => True
              | (None, None) => True
            end);
    

    (** * minus **)
    map_minus_sem:
      (** def1 **)
      forall m m1 a,
        usePerm = false ->
        get (minus m m1) a 
        = match (get m a, get m1 a) with
            | (Some b, Some b1) => None
            | (Some b1, None) => Some b1
            | (None, Some b2) => None
            | (None, None) => None
          end;

    map_minus_semp:
      (** def2 **)
      forall m1 m a,
        usePerm = true ->
        get (minus m m1) a
        = match (get m a, get m1 a) with
            | (Some b, Some b1) =>
              match (same b (flip b1)) return (option B) with
                | true => match (isRw b) with
                             | true => Some b1
                             | false => None
                           end
                | false => None
              end
            | (Some b, None) => Some b
            | (None, Some b1) => None
            | (None, None) => None
          end;
    
    map_join_minus:
      forall z x,
        (exists y, join x y z) ->
        join x (minus z x) z;

    (** * del **)
    map_del_sem:
      forall m a t,
        get (del m a) t
        = match (map_dec_a a t) with
            | left _ => None
            | right _ => get m t
          end
    }.

Definition indom {A B T:Type} {MC: PermMap A B T} (x: T) (t: A) :=
  exists v, get x t = Some v.

Definition sub {A B T:Type} {MC: PermMap A B T} (x y:T) :=
  (** x is subset of y **)
  exists x', join x x' y.

Definition disjoint {A B T:Type} {MC:PermMap A B T} x y :=
  exists z, join x y z.

Definition joinsig {A B T:Type} {MC:PermMap A B T} x y m M :=
  join (sig x y) m M.

Definition eqdom {A B T:Type} {MC:PermMap A B T} M1 M2 :=
  forall x, indom M1 x <-> indom M2 x.

(** inform simpl not to unfold these keywords **)
Arguments usePerm : simpl never.
Arguments isRw : simpl never.
Arguments flip : simpl never.
Arguments sameV : simpl never.

Arguments sig : simpl never.
Arguments set : simpl never.
Arguments get : simpl never.
Arguments join : simpl never.
Arguments emp : simpl never.
Arguments merge : simpl never.
Arguments minus : simpl never.
Arguments del : simpl never.

