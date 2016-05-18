(** Logic-Enriched Type Theories **)
(** following the formulation in Classical Predicate Logic-Enriched Type Theories**)
(** By Robin Adams, Zhaohui Luo **)

(** LTTw **)

(** LTTw consists of type theory (constructive) part and logics part (propositions) **)


datatype TYPE = NAT | PROD of TYPE * TYPE | FUN of TYPE * TYPE | SET of TYPE | U
and Type = Nat | Prod of Type * Type (* type names *)
and Term = Var of string | O | S of Term | Lam of string * TYPE * Term * TYPE | App of TYPE * Term * Term
           | Pair of TYPE * Term * Term | Pr1 of TYPE * Term | Pr2 of TYPE * Term
           | En of string * TYPE * Term * string * string * Term * Term (* NAT eliminator *)
           | Set of string * TYPE * Prop
and PROP = EQ of Type * Term * Term | BOT | IMP of PROP * PROP | FORALL of string * TYPE * PROP (* small prop *)
and Prop = Eq of Type * Term * Term | Bot | Imp of Prop * Prop | Forall of string * Type * Prop


(** Contexts **)

(** variable name : TYPE **)
type Ctxt = (string * TYPE) list

fun remove a xs =
  case xs of
      [] => []
    | x::xs => if x = a then remove a xs else x :: (remove a xs)

(** collect free variables of an expression as a list **)
fun FV e =
  case e of
      VAR (x,_) => [x]
   |  LAM (x,t,e,_) => remove x (FV e @ FV t)
   |  APP (m,n,_) => (FV m) @ (FV n)
   |  PI  (x,A,B,_) => remove x (FV A @ FV B)
   |  PAIR (a,b,_) => (FV a) @ (FV b)
   |  PR1 (p,_) => FV p
   |  PR2 (p,_) => FV p
   |  SIG (x,A,B,_) => remove x (FV A @ FV B)
   |  EQ  (A,x,y,_) => FV A @ FV x @ FV y
   |  REFL (A,_) => FV A
   |  TYPE _ => []

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
