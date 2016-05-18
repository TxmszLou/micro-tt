(** Logic-Enriched Type Theories **)
(** following the formulation in Classical Predicate Logic-Enriched Type Theories**)
(** By Robin Adams, Zhaohui Luo **)

(** LTTw **)

(** LTTw consists of type theory (constructive) part and logics part (propositions) **)


datatype TYPE = NAT | PROD of TYPE * TYPE | FUN of TYPE * TYPE | SET of TYPE | U
and Type = Nat | Prod of Type * Type (* type names *)
(* lots of type annotation *)
and Term = Var of string | O | S of Term | Lam of string * TYPE * Term * TYPE | App of Term * Term
           | Pair of TYPE * Term * Term | Pr1 of TYPE * Term | Pr2 of TYPE * Term
           | En of string * TYPE * Term * string * string * Term * Term (* NAT eliminator *)
           | Set of string * TYPE * Prop
and PROP = EQ of Type * Term * Term | BOT | IMP of PROP * PROP | FORALL of string * TYPE * PROP (* small prop *)
and Prop = Eq of Type * Term * Term | Bot | Imp of Prop * Prop | Forall of string * Type * Prop

datatype Expr = TY of TYPE | Ty of Type | Tm of Term | PR of PROP | Pr of Prop


(** Contexts **)

(** variable name : TYPE **)
type Ctxt = (string * TYPE) list

fun remove a xs =
  case xs of
      [] => []
    | x::xs => if x = a then remove a xs else x :: (remove a xs)

(** collect free variables of an expression as a list **)
fun FV (e : Expr) =
  case e of
      TY t =>
      (case t of
           NAT => []
         | PROD(M,N) => FV (TY M) @ FV (TY N)
         | FUN(A,B) => FV (TY A) @ FV (TY B)
         | SET t => FV (TY t)
         | U => [])
    | Ty t =>
      (case t of
           Nat => []
        | Prod(m,n) => FV (Ty m) @ FV (Ty n)
      )
    | Tm t =>
      (case t of
           Var x => [x]
         | O => []
         | S n => FV (Tm n)
         | Lam(x,_,m,_) => remove x (FV (Tm m))
         | App(m,n) => FV (Tm m) @ FV (Tm n)
         | Pair(_,a,b) => FV (Tm a) @ FV (Tm b)
         | Pr1(_,p) => FV (Tm p)
         | Pr2(_,p) => FV (Tm p)
         | En(_,_,L,y,z,M,_) => FV (Tm L) @ remove y (remove z (FV (Tm M)))
         | Set(x,_,_) => [x])
    | PR p => []
    | Pr _ => []


fun member x xs =
  case xs of
      [] => false
    | y::xs => if x = y then true else member x xs


(** name -> denotation function **)
(** T(-) : Type -> TYPE **)

fun T (M : Type) =
  case M of
      Nat => NAT
   |  Prod(M,N) => PROD(T M, T N)

(** V(-) : Prop -> PROP **)

fun V (p : Prop) : PROP =
  case p of
     Eq(L,M,N) => EQ(L,M,N)
   | Bot => BOT
   | Imp(p,q) => IMP(V p, V q)
   | Forall(x,m,p) => FORALL(x,T m,V p)

(** type theory **)
