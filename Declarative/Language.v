(* generated by Ott 0.30, locally-nameless from: Declarative/Language.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Ott.ott_list_core.
(** syntax *)
Definition exprvar : Set := var. (*r variables *)
Definition number : Set := nat. (*r numbers *)

Inductive kind : Set :=  (*r kind *)
 | k_star : kind (*r type of type *)
 | k_box : kind (*r type of type of type *).

Inductive expr : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variable *)
 | e_var_f (x:exprvar) (*r variable *)
 | e_kind (k:kind) (*r type of type *)
 | e_num (n:number) (*r integer value *)
 | e_int : expr (*r integer type *)
 | e_app (e1:expr) (e2:expr) (*r application *)
 | e_abs (A:expr) (e:expr) (*r abstraction *)
 | e_pi (A:expr) (B:expr) (*r dependent product *)
 | e_all (A:expr) (B:expr) (*r implicit function type *)
 | e_bind (A:expr) (e:expr) (*r implicit lambda *)
 | e_castup (A:expr) (e:expr) (*r cast up *)
 | e_castdn (B:expr) (e:expr) (*r cast down *).

Inductive eexpr : Set :=  (*r extracted expression *)
 | ee_var_b (_:nat)
 | ee_var_f (x:exprvar)
 | ee_kind (k:kind)
 | ee_num (n:number)
 | ee_int : eexpr
 | ee_app (ee1:eexpr) (ee2:eexpr)
 | ee_abs (ee:eexpr)
 | ee_bind (ee:eexpr)
 | ee_pi (eA:eexpr) (eB:eexpr)
 | ee_all (eA:eexpr) (eB:eexpr).

Definition context : Set := (list (exprvar * expr)).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_eexpr_wrt_eexpr_rec (k:nat) (ee_5:eexpr) (ee__6:eexpr) {struct ee__6}: eexpr :=
  match ee__6 with
  | (ee_var_b nat) => if (k === nat) then ee_5 else (ee_var_b nat)
  | (ee_var_f x) => ee_var_f x
  | (ee_kind k) => ee_kind k
  | (ee_num n) => ee_num n
  | ee_int => ee_int 
  | (ee_app ee1 ee2) => ee_app (open_eexpr_wrt_eexpr_rec k ee_5 ee1) (open_eexpr_wrt_eexpr_rec k ee_5 ee2)
  | (ee_abs ee) => ee_abs (open_eexpr_wrt_eexpr_rec (S k) ee_5 ee)
  | (ee_bind ee) => ee_bind (open_eexpr_wrt_eexpr_rec (S k) ee_5 ee)
  | (ee_pi eA eB) => ee_pi (open_eexpr_wrt_eexpr_rec k ee_5 eA) (open_eexpr_wrt_eexpr_rec (S k) ee_5 eB)
  | (ee_all eA eB) => ee_all (open_eexpr_wrt_eexpr_rec k ee_5 eA) (open_eexpr_wrt_eexpr_rec (S k) ee_5 eB)
end.

Fixpoint open_expr_wrt_expr_rec (k:nat) (e_5:expr) (e__6:expr) {struct e__6}: expr :=
  match e__6 with
  | (e_var_b nat) => if (k === nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_kind k) => e_kind k
  | (e_num n) => e_num n
  | e_int => e_int 
  | (e_app e1 e2) => e_app (open_expr_wrt_expr_rec k e_5 e1) (open_expr_wrt_expr_rec k e_5 e2)
  | (e_abs A e) => e_abs (open_expr_wrt_expr_rec k e_5 A) (open_expr_wrt_expr_rec (S k) e_5 e)
  | (e_pi A B) => e_pi (open_expr_wrt_expr_rec k e_5 A) (open_expr_wrt_expr_rec (S k) e_5 B)
  | (e_all A B) => e_all (open_expr_wrt_expr_rec k e_5 A) (open_expr_wrt_expr_rec (S k) e_5 B)
  | (e_bind A e) => e_bind (open_expr_wrt_expr_rec k e_5 A) (open_expr_wrt_expr_rec (S k) e_5 e)
  | (e_castup A e) => e_castup (open_expr_wrt_expr_rec k e_5 A) (open_expr_wrt_expr_rec k e_5 e)
  | (e_castdn B e) => e_castdn (open_expr_wrt_expr_rec k e_5 B) (open_expr_wrt_expr_rec k e_5 e)
end.

Definition open_eexpr_wrt_eexpr ee_5 ee__6 := open_eexpr_wrt_eexpr_rec 0 ee__6 ee_5.

Definition open_expr_wrt_expr e_5 e__6 := open_expr_wrt_expr_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_expr *)
Inductive lc_expr : expr -> Prop :=    (* defn lc_expr *)
 | lc_e_var_f : forall (x:exprvar),
     (lc_expr (e_var_f x))
 | lc_e_kind : forall (k:kind),
     (lc_expr (e_kind k))
 | lc_e_num : forall (n:number),
     (lc_expr (e_num n))
 | lc_e_int : 
     (lc_expr e_int)
 | lc_e_app : forall (e1 e2:expr),
     (lc_expr e1) ->
     (lc_expr e2) ->
     (lc_expr (e_app e1 e2))
 | lc_e_abs : forall (L:vars) (A e:expr),
     (lc_expr A) ->
      ( forall x , x \notin  L  -> lc_expr  ( open_expr_wrt_expr e (e_var_f x) )  )  ->
     (lc_expr (e_abs A e))
 | lc_e_pi : forall (L:vars) (A B:expr),
     (lc_expr A) ->
      ( forall x , x \notin  L  -> lc_expr  ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     (lc_expr (e_pi A B))
 | lc_e_all : forall (L:vars) (A B:expr),
     (lc_expr A) ->
      ( forall x , x \notin  L  -> lc_expr  ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     (lc_expr (e_all A B))
 | lc_e_bind : forall (L:vars) (A e:expr),
     (lc_expr A) ->
      ( forall x , x \notin  L  -> lc_expr  ( open_expr_wrt_expr e (e_var_f x) )  )  ->
     (lc_expr (e_bind A e))
 | lc_e_castup : forall (A e:expr),
     (lc_expr A) ->
     (lc_expr e) ->
     (lc_expr (e_castup A e))
 | lc_e_castdn : forall (B e:expr),
     (lc_expr B) ->
     (lc_expr e) ->
     (lc_expr (e_castdn B e)).

(* defns LC_eexpr *)
Inductive lc_eexpr : eexpr -> Prop :=    (* defn lc_eexpr *)
 | lc_ee_var_f : forall (x:exprvar),
     (lc_eexpr (ee_var_f x))
 | lc_ee_kind : forall (k:kind),
     (lc_eexpr (ee_kind k))
 | lc_ee_num : forall (n:number),
     (lc_eexpr (ee_num n))
 | lc_ee_int : 
     (lc_eexpr ee_int)
 | lc_ee_app : forall (ee1 ee2:eexpr),
     (lc_eexpr ee1) ->
     (lc_eexpr ee2) ->
     (lc_eexpr (ee_app ee1 ee2))
 | lc_ee_abs : forall (L:vars) (ee:eexpr),
      ( forall x , x \notin  L  -> lc_eexpr  ( open_eexpr_wrt_eexpr ee (ee_var_f x) )  )  ->
     (lc_eexpr (ee_abs ee))
 | lc_ee_bind : forall (L:vars) (ee:eexpr),
      ( forall x , x \notin  L  -> lc_eexpr  ( open_eexpr_wrt_eexpr ee (ee_var_f x) )  )  ->
     (lc_eexpr (ee_bind ee))
 | lc_ee_pi : forall (L:vars) (eA eB:eexpr),
     (lc_eexpr eA) ->
      ( forall x , x \notin  L  -> lc_eexpr  ( open_eexpr_wrt_eexpr eB (ee_var_f x) )  )  ->
     (lc_eexpr (ee_pi eA eB))
 | lc_ee_all : forall (L:vars) (eA eB:eexpr),
     (lc_eexpr eA) ->
      ( forall x , x \notin  L  -> lc_eexpr  ( open_eexpr_wrt_eexpr eB (ee_var_f x) )  )  ->
     (lc_eexpr (ee_all eA eB)).
(** free variables *)
Fixpoint fv_expr (e_5:expr) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_kind k) => {}
  | (e_num n) => {}
  | e_int => {}
  | (e_app e1 e2) => (fv_expr e1) \u (fv_expr e2)
  | (e_abs A e) => (fv_expr A) \u (fv_expr e)
  | (e_pi A B) => (fv_expr A) \u (fv_expr B)
  | (e_all A B) => (fv_expr A) \u (fv_expr B)
  | (e_bind A e) => (fv_expr A) \u (fv_expr e)
  | (e_castup A e) => (fv_expr A) \u (fv_expr e)
  | (e_castdn B e) => (fv_expr B) \u (fv_expr e)
end.

Fixpoint fv_eexpr (ee_5:eexpr) : vars :=
  match ee_5 with
  | (ee_var_b nat) => {}
  | (ee_var_f x) => {{x}}
  | (ee_kind k) => {}
  | (ee_num n) => {}
  | ee_int => {}
  | (ee_app ee1 ee2) => (fv_eexpr ee1) \u (fv_eexpr ee2)
  | (ee_abs ee) => (fv_eexpr ee)
  | (ee_bind ee) => (fv_eexpr ee)
  | (ee_pi eA eB) => (fv_eexpr eA) \u (fv_eexpr eB)
  | (ee_all eA eB) => (fv_eexpr eA) \u (fv_eexpr eB)
end.

(** substitutions *)
Fixpoint subst_expr (e_5:expr) (x5:exprvar) (e__6:expr) {struct e__6} : expr :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_kind k) => e_kind k
  | (e_num n) => e_num n
  | e_int => e_int 
  | (e_app e1 e2) => e_app (subst_expr e_5 x5 e1) (subst_expr e_5 x5 e2)
  | (e_abs A e) => e_abs (subst_expr e_5 x5 A) (subst_expr e_5 x5 e)
  | (e_pi A B) => e_pi (subst_expr e_5 x5 A) (subst_expr e_5 x5 B)
  | (e_all A B) => e_all (subst_expr e_5 x5 A) (subst_expr e_5 x5 B)
  | (e_bind A e) => e_bind (subst_expr e_5 x5 A) (subst_expr e_5 x5 e)
  | (e_castup A e) => e_castup (subst_expr e_5 x5 A) (subst_expr e_5 x5 e)
  | (e_castdn B e) => e_castdn (subst_expr e_5 x5 B) (subst_expr e_5 x5 e)
end.

Fixpoint subst_eexpr (ee_5:eexpr) (x5:exprvar) (ee__6:eexpr) {struct ee__6} : eexpr :=
  match ee__6 with
  | (ee_var_b nat) => ee_var_b nat
  | (ee_var_f x) => (if eq_var x x5 then ee_5 else (ee_var_f x))
  | (ee_kind k) => ee_kind k
  | (ee_num n) => ee_num n
  | ee_int => ee_int 
  | (ee_app ee1 ee2) => ee_app (subst_eexpr ee_5 x5 ee1) (subst_eexpr ee_5 x5 ee2)
  | (ee_abs ee) => ee_abs (subst_eexpr ee_5 x5 ee)
  | (ee_bind ee) => ee_bind (subst_eexpr ee_5 x5 ee)
  | (ee_pi eA eB) => ee_pi (subst_eexpr ee_5 x5 eA) (subst_eexpr ee_5 x5 eB)
  | (ee_all eA eB) => ee_all (subst_eexpr ee_5 x5 eA) (subst_eexpr ee_5 x5 eB)
end.

Fixpoint extract (e : expr) : eexpr :=
  match e with
  | e_var_b n => ee_var_b n
  | e_var_f x => ee_var_f x
  | e_kind k  => ee_kind k
  | e_num n   => ee_num n
  | e_int     => ee_int
  | e_app  f a => ee_app  (extract f) (extract a)
  | e_abs  A b => ee_abs  (extract b)
  | e_bind A b => ee_bind (extract b)
  | e_pi   A B => ee_pi   (extract A) (extract B)
  | e_all  A B => ee_all  (extract A) (extract B)
  | e_castup A e => extract e
  | e_castdn A e => extract e
  end
.


(** definitions *)

(* defns MonoType *)
Inductive mono_type : expr -> Prop :=    (* defn mono_type *)
 | mono_kind : forall (k:kind),
     mono_type (e_kind k)
 | mono_var : forall (x:exprvar),
     mono_type (e_var_f x)
 | mono_int : 
     mono_type e_int
 | mono_lit : forall (n:number),
     mono_type (e_num n)
 | mono_app : forall (e1 e2:expr),
      mono_type e1  ->
     mono_type e2 ->
     mono_type  ( (e_app e1 e2) ) 
 | mono_pi : forall (L:vars) (A B:expr),
      mono_type A  ->
      ( forall x , x \notin  L  -> mono_type  ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     mono_type (e_pi A B)
 | mono_lambda : forall (L:vars) (A B:expr),
      mono_type A  ->
      ( forall x , x \notin  L  -> mono_type  ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     mono_type (e_abs A B)
 | mono_bind : forall (L:vars) (A B:expr),
      mono_type A  ->
      ( forall x , x \notin  L  -> mono_type  ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     mono_type (e_bind A B)
 | mono_castup : forall (A e:expr),
      mono_type A  ->
     mono_type e ->
     mono_type (e_castup A e)
 | mono_castdn : forall (B e:expr),
      mono_type B  ->
     mono_type e ->
     mono_type (e_castdn B e).

(* defns Value *)
Inductive value : expr -> Prop :=    (* defn value *)
 | v_kind : forall (k:kind),
     value (e_kind k)
 | v_num : forall (n:number),
     value (e_num n)
 | v_int : 
     value e_int
 | v_abs : forall (A e:expr),
     lc_expr A ->
     lc_expr (e_abs A e) ->
     value (e_abs A e)
 | v_bind : forall (A e:expr),
     lc_expr A ->
     lc_expr (e_bind A e) ->
     value (e_bind A e)
 | v_pi : forall (A B:expr),
     lc_expr A ->
     lc_expr (e_pi A B) ->
     value (e_pi A B)
 | v_all : forall (A B:expr),
     lc_expr A ->
     lc_expr (e_all A B) ->
     value (e_all A B)
 | v_castup : forall (A e:expr),
     lc_expr A ->
     value e ->
     value (e_castup A e).

(* defns Reduce *)
Inductive reduce : expr -> expr -> Prop :=    (* defn reduce *)
 | r_app : forall (e1 e3 e2:expr),
     lc_expr e3 ->
     reduce e1 e2 ->
     reduce (e_app e1 e3) (e_app e2 e3)
 | r_beta : forall (A e1 e2:expr),
     lc_expr A ->
     lc_expr (e_abs A e1) ->
     lc_expr e2 ->
     reduce (e_app  ( (e_abs A e1) )  e2)  (open_expr_wrt_expr  e1   e2 ) 
 | r_inst : forall (A e1 e2 e:expr),
     lc_expr A ->
     lc_expr (e_bind A e1) ->
     lc_expr e2 ->
     mono_type e ->
     reduce (e_app  ( (e_bind A e1) )  e2) (e_app  (  (open_expr_wrt_expr  e1   e )  )  e2)
 | r_castup : forall (A e1 e2:expr),
     lc_expr A ->
     reduce e1 e2 ->
     reduce (e_castup A e1) (e_castup A e2)
 | r_castdn : forall (A e1 e2:expr),
     lc_expr A ->
     reduce e1 e2 ->
     reduce (e_castdn A e1) (e_castdn A e2)
 | r_cast_elim : forall (A B e:expr),
     lc_expr A ->
     lc_expr B ->
     value e ->
     reduce (e_castdn A  ( (e_castup B e) ) ) e.

(* defns ExtractedValue *)
Inductive evalue : eexpr -> Prop :=    (* defn evalue *)
 | ev_kind : forall (k:kind),
     evalue (ee_kind k)
 | ev_num : forall (n:number),
     evalue (ee_num n)
 | ev_int : 
     evalue ee_int
 | ev_abs : forall (ee:eexpr),
     lc_eexpr (ee_abs ee) ->
     evalue (ee_abs ee)
 | ev_bind : forall (ee:eexpr),
     lc_eexpr (ee_bind ee) ->
     evalue (ee_bind ee)
 | ev_pi : forall (eA eB:eexpr),
     lc_eexpr eA ->
     lc_eexpr (ee_pi eA eB) ->
     evalue (ee_pi eA eB)
 | ev_all : forall (eA eB:eexpr),
     lc_eexpr eA ->
     lc_eexpr (ee_all eA eB) ->
     evalue (ee_all eA eB).

(* defns ExtractedReduce *)
Inductive ereduce : eexpr -> eexpr -> Prop :=    (* defn ereduce *)
 | er_app : forall (ee1 ee3 ee2:eexpr),
     lc_eexpr ee3 ->
     ereduce ee1 ee2 ->
     ereduce (ee_app ee1 ee3) (ee_app ee2 ee3)
 | er_beta : forall (ee1 ee2:eexpr),
     lc_eexpr (ee_abs ee1) ->
     lc_eexpr ee2 ->
     ereduce (ee_app  ( (ee_abs ee1) )  ee2)  (open_eexpr_wrt_eexpr  ee1   ee2 ) 
 | er_elim : forall (L:vars) (ee1 ee2:eexpr),
     lc_eexpr (ee_bind ee1) ->
     lc_eexpr ee2 ->
      ( forall x , x \notin  L  -> ereduce (ee_app  ( (ee_bind ee1) )  ee2) (ee_app  ( open_eexpr_wrt_eexpr ee1 (ee_var_f x) )  ee2) ) .

(* defns UnifiedSubtyping *)
Inductive wf_context : context -> Prop :=    (* defn wf_context *)
 | wf_nil : 
     wf_context  nil 
 | wf_cons : forall (G:context) (x:exprvar) (A:expr) (k:kind),
      wf_context G  ->
       ( x  `notin` dom  G )   ->
      (usub  G   A   A   (e_kind k) )  ->
     wf_context  (( x ,  A ) ::  G ) 
with usub : context -> expr -> expr -> expr -> Prop :=    (* defn usub *)
 | s_var : forall (G:context) (x:exprvar) (A:expr),
      wf_context G  ->
      (binds  x   A   G )  ->
     usub G (e_var_f x) (e_var_f x) A
 | s_lit : forall (G:context) (n:number),
     wf_context G ->
     usub G (e_num n) (e_num n) e_int
 | s_star : forall (G:context),
     wf_context G ->
     usub G (e_kind k_star) (e_kind k_star) (e_kind k_box)
 | s_int : forall (G:context),
     wf_context G ->
     usub G e_int e_int (e_kind k_star)
 | s_abs : forall (L:vars) (G:context) (A e1 e2 B:expr) (k2:kind),
      ( forall x , x \notin  L  ->  (usub   (( x ,  A ) ::  G )     ( open_expr_wrt_expr B (e_var_f x) )     ( open_expr_wrt_expr B (e_var_f x) )    (e_kind k2) )  )  ->
      ( forall x , x \notin  L  -> usub  (( x ,  A ) ::  G )   ( open_expr_wrt_expr e1 (e_var_f x) )   ( open_expr_wrt_expr e2 (e_var_f x) )   ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     usub G (e_abs A e1) (e_abs A e2) (e_pi A B)
 | s_pi : forall (L:vars) (G:context) (A1 B1 A2 B2:expr) (k2 k1:kind),
     usub G A2 A1 (e_kind k1) ->
      ( forall x , x \notin  L  ->   (usub   (( x ,  A1 ) ::  G )     ( open_expr_wrt_expr B1 (e_var_f x) )     ( open_expr_wrt_expr B1 (e_var_f x) )    (e_kind k2) )   )  ->
      ( forall x , x \notin  L  -> usub  (( x ,  A2 ) ::  G )   ( open_expr_wrt_expr B1 (e_var_f x) )   ( open_expr_wrt_expr B2 (e_var_f x) )  (e_kind k2) )  ->
     usub G (e_pi A1 B1) (e_pi A2 B2) (e_kind k2)
 | s_app : forall (G:context) (e1 e e2 B A:expr),
      mono_type e  ->
      (usub  G   e   e   A )  ->
     usub G e1 e2 (e_pi A B) ->
     usub G (e_app e1 e) (e_app e2 e)  (open_expr_wrt_expr  B   e ) 
 | s_bind : forall (L:vars) (G:context) (A e1 e2 B:expr),
      ( forall x , x \notin  L  ->  (usub   (( x ,  A ) ::  G )     ( open_expr_wrt_expr B (e_var_f x) )     ( open_expr_wrt_expr B (e_var_f x) )    (e_kind k_star) )  )  ->
      ( forall x , x \notin  L  -> usub  (( x ,  A ) ::  G )   ( open_expr_wrt_expr e1 (e_var_f x) )   ( open_expr_wrt_expr e2 (e_var_f x) )   ( open_expr_wrt_expr B (e_var_f x) )  )  ->
      ( forall x , x \notin  L  ->   ( x  `notin` fv_eexpr (extract   ( open_expr_wrt_expr e1 (e_var_f x) )  ))   )  ->
      ( forall x , x \notin  L  ->  ( x  `notin` fv_eexpr (extract   ( open_expr_wrt_expr e2 (e_var_f x) )  ))  )  ->
     usub G (e_bind A e1) (e_bind A e2) (e_all A B)
 | s_castup : forall (G:context) (A e1 e2:expr) (k:kind) (B:expr),
      (usub  G   A   A   (e_kind k) )  ->
     reduce A B ->
     usub G e1 e2 B ->
     usub G (e_castup A e1) (e_castup A e2) A
 | s_castdn : forall (G:context) (B e1 e2 A:expr) (k:kind),
      (usub  G   B   B   (e_kind k) )  ->
     reduce A B ->
     usub G e1 e2 A ->
     usub G (e_castdn B e1) (e_castdn B e2) A
 | s_forall_l : forall (L:vars) (G:context) (A B C e:expr),
     mono_type e ->
      (usub  G   e   e   A )  ->
      usub G  (open_expr_wrt_expr  B   e )  C (e_kind k_star)  ->
      ( forall x , x \notin  L  ->  (usub   (( x ,  A ) ::  G )     ( open_expr_wrt_expr B (e_var_f x) )     ( open_expr_wrt_expr B (e_var_f x) )    (e_kind k_star) )  )  ->
     usub G (e_all A B) C (e_kind k_star)
 | s_forall_r : forall (L:vars) (G:context) (A B C:expr),
      (usub  G   A   A   (e_kind k_star) )  ->
      ( forall x , x \notin  L  -> usub  (( x ,  B ) ::  G )  A  ( open_expr_wrt_expr C (e_var_f x) )  (e_kind k_star) )  ->
     usub G A (e_all B C) (e_kind k_star)
 | s_forall : forall (L:vars) (G:context) (A B C:expr),
      ( forall x , x \notin  L  -> usub  (( x ,  A ) ::  G )   ( open_expr_wrt_expr B (e_var_f x) )   ( open_expr_wrt_expr C (e_var_f x) )  (e_kind k_star) )  ->
     usub G (e_all A B) (e_all A C) (e_kind k_star)
 | s_sub : forall (G:context) (e1 e2 B A:expr) (k:kind),
      usub G e1 e2 A  ->
     usub G A B (e_kind k) ->
     usub G e1 e2 B.

(* defns SimplifiedUnifiedSubtyping *)
Inductive swf_context : context -> Prop :=    (* defn swf_context *)
 | swf_nil : 
     swf_context  nil 
 | swf_cons : forall (G:context) (x:exprvar) (A:expr) (k:kind),
      swf_context G  ->
       ( x  `notin` dom  G )   ->
      susub  G   A   A   (e_kind k)  ->
     swf_context  (( x ,  A ) ::  G ) 
with susub : context -> expr -> expr -> expr -> Prop :=    (* defn susub *)
 | ss_var : forall (G:context) (x:exprvar) (A:expr),
      swf_context G  ->
      (binds  x   A   G )  ->
     susub G (e_var_f x) (e_var_f x) A
 | ss_lit : forall (G:context) (n:number),
     swf_context G ->
     susub G (e_num n) (e_num n) e_int
 | ss_star : forall (G:context),
     swf_context G ->
     susub G (e_kind k_star) (e_kind k_star) (e_kind k_box)
 | ss_int : forall (G:context),
     swf_context G ->
     susub G e_int e_int (e_kind k_star)
 | ss_abs : forall (L:vars) (G:context) (A e1 e2 B:expr) (k2:kind),
      ( forall x , x \notin  L  ->   susub   (( x ,  A ) ::  G )     ( open_expr_wrt_expr B (e_var_f x) )     ( open_expr_wrt_expr B (e_var_f x) )    (e_kind k2)   )  ->
      ( forall x , x \notin  L  -> susub  (( x ,  A ) ::  G )   ( open_expr_wrt_expr e1 (e_var_f x) )   ( open_expr_wrt_expr e2 (e_var_f x) )   ( open_expr_wrt_expr B (e_var_f x) )  )  ->
     susub G (e_abs A e1) (e_abs A e2) (e_pi A B)
 | ss_pi : forall (L:vars) (G:context) (A1 B1 A2 B2:expr) (k2 k1:kind),
     susub G A2 A1 (e_kind k1) ->
      ( forall x , x \notin  L  ->   susub   (( x ,  A1 ) ::  G )     ( open_expr_wrt_expr B1 (e_var_f x) )     ( open_expr_wrt_expr B1 (e_var_f x) )    (e_kind k2)   )  ->
      ( forall x , x \notin  L  -> susub  (( x ,  A2 ) ::  G )   ( open_expr_wrt_expr B1 (e_var_f x) )   ( open_expr_wrt_expr B2 (e_var_f x) )  (e_kind k2) )  ->
     susub G (e_pi A1 B1) (e_pi A2 B2) (e_kind k2)
 | ss_app : forall (G:context) (e1 e e2 B A:expr),
      mono_type e  ->
      susub  G   e   e   A  ->
     susub G e1 e2 (e_pi A B) ->
     susub G (e_app e1 e) (e_app e2 e)  (open_expr_wrt_expr  B   e ) 
 | ss_bind : forall (L:vars) (G:context) (A e1 e2 B:expr),
      ( forall x , x \notin  L  ->  susub   (( x ,  A ) ::  G )     ( open_expr_wrt_expr B (e_var_f x) )     ( open_expr_wrt_expr B (e_var_f x) )    (e_kind k_star)  )  ->
      ( forall x , x \notin  L  -> susub  (( x ,  A ) ::  G )   ( open_expr_wrt_expr e1 (e_var_f x) )   ( open_expr_wrt_expr e2 (e_var_f x) )   ( open_expr_wrt_expr B (e_var_f x) )  )  ->
      ( forall x , x \notin  L  ->   ( x  `notin` fv_eexpr (extract   ( open_expr_wrt_expr e1 (e_var_f x) )  ))   )  ->
      ( forall x , x \notin  L  ->  ( x  `notin` fv_eexpr (extract   ( open_expr_wrt_expr e2 (e_var_f x) )  ))  )  ->
     susub G (e_bind A e1) (e_bind A e2) (e_all A B)
 | ss_castup : forall (G:context) (A e1 e2:expr) (k:kind) (B:expr),
      susub  G   A   A   (e_kind k)  ->
     reduce A B ->
     susub G e1 e2 B ->
     susub G (e_castup A e1) (e_castup A e2) A
 | ss_castdn : forall (G:context) (B e1 e2 A:expr) (k:kind),
      susub  G   B   B   (e_kind k)  ->
     reduce A B ->
     susub G e1 e2 A ->
     susub G (e_castdn B e1) (e_castdn B e2) A
 | ss_forall_l : forall (L:vars) (G:context) (A B C e:expr),
      mono_type e  ->
      susub  G   e   e   A  ->
      susub G  (open_expr_wrt_expr  B   e )  C (e_kind k_star)  ->
      ( forall x , x \notin  L  ->  susub   (( x ,  A ) ::  G )     ( open_expr_wrt_expr B (e_var_f x) )     ( open_expr_wrt_expr B (e_var_f x) )    (e_kind k_star)  )  ->
     susub G (e_all A B) C (e_kind k_star)
 | ss_forall_r : forall (L:vars) (G:context) (A B C:expr),
       susub  G   A   A   (e_kind k_star)   ->
      ( forall x , x \notin  L  -> susub  (( x ,  B ) ::  G )  A  ( open_expr_wrt_expr C (e_var_f x) )  (e_kind k_star) )  ->
     susub G A (e_all B C) (e_kind k_star)
 | ss_forall : forall (L:vars) (G:context) (A B C:expr),
      ( forall x , x \notin  L  -> susub  (( x ,  A ) ::  G )   ( open_expr_wrt_expr B (e_var_f x) )   ( open_expr_wrt_expr C (e_var_f x) )  (e_kind k_star) )  ->
     susub G (e_all A B) (e_all A C) (e_kind k_star)
 | ss_sub : forall (G:context) (e1 e2 B A:expr) (k:kind),
      susub G e1 e2 A  ->
     susub G A B (e_kind k) ->
     susub G e1 e2 B.


(** infrastructure *)
Hint Constructors mono_type value reduce evalue ereduce wf_context usub swf_context susub lc_expr lc_eexpr : core.


