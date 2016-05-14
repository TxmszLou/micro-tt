(* constants introduction, type checking, type synthesizing *)

(* a minimal type theory with universes *)
(**

t,u,A,B ::= x | lambda x : A . t | t u | Pi (x : A) . B
         | Eq A t u | refl A a | Type_i

+ naive universes (cumulative universe)
+ hints (for reflection rules)

*)
datatype Term = Var of string * int | Lam of string * Term * Term * int | App of Term * Term * int
              | Pi of string * Term * Term * int | Eq of Term * Term * Term * int | refl of Term * Term * int
              | Type of int


type Ctxt = (Term * Term) list

(** (e1 = e1' : A) list **)
type Hint = (Term * Term * Term) list

fun remove a xs =
  case xs of
      [] => []
    | x::xs => if x = a then remove a xs else x :: (remove a xs)

(** collect free variables of an expression as a list **)
fun FV e =
  case e of
      Var (x,_) => [x]
   |  Lam (x,t,e,_) => remove x ((FV e) @ (FV t))
   |  App (m,n,_) => (FV m) @ (FV n)
   |  Pi  (x,A,B,_) => remove x ((FV A) @ (FV B))
   |  Eq  (A,x,y,_) => (FV A) @ (FV x) @ (FV y)
   |  refl (A,x,_) => (FV A) @ (FV x)
   |  Type _ => []

fun member x xs =
  case xs of
      [] => false
    | y::xs => if x = y then true else member x xs

(** invariant: **)
(** (1) each term is tupled with a number representing next free variable to be generated in the term **)
(** (2) fresh variable number of the term is always greater than that of its subterms **)
fun subst (e : Term) (x : string) (m : Term) : Term =
  case e of
      Var (y,_) => if x = y then m else e
    | Lam (y,t,n,c) => if x = y
                       then e
                       else if member y (FV m)
                       then
                           let val nvar = "T" ^ (Int.toString c)
                           in Lam(nvar,t,(subst (subst n y (Var (nvar,c+1))) x m),c+1)
                           end
                       else
                           (Lam(y,t,(subst n x m),c))
    |  App (e1,e2,c) => App (subst e1 x m, subst e2 x m,c)
    |  Pi (y,A,B,c) => if x = y
                         then e
                         else if member y (FV m)
                         then
                             let val nvar = "T" ^ (Int.toString c)
                             in Pi (nvar,(subst (subst A y (Var (nvar,c+1))) x m),
                                         (subst (subst B y (Var (nvar,c+1))) x m),c+1)
                             end
                         else
                             (Pi (y,(subst A x m),(subst B x m),c))
    |  Eq (A,a,b,c) => Eq (subst A x m, subst a x m, subst b x m,c)
    |  refl (A,a,c) => refl (subst A x m, subst a x m,c)
    |  Type _ => e

(** alpha-congruence **)
fun alpha (s : Term) (t : Term) : bool =
  case (s,t) of
      (Var x, Var y) => x = y
    | (Lam(x,t,m,_),(Lam(y,t',n,_))) => (alpha t t') andalso (alpha m (subst n y (Var (x,0))))
    | (App(e1,e2,_),App(t1,t2,_)) => (alpha e1 t1) andalso (alpha e2 t2)
    | (Pi(x,A,B,_),Pi(y,C,D,_)) => (alpha A C) andalso (alpha B (subst D y (Var (x,0))))
    | (Eq(A,a,b,_),Eq(B,x,y,_)) => (alpha A B) andalso (alpha a x) andalso (alpha b y)
    | (refl(A,x,_),refl(B,y,_)) => (alpha A B) andalso (alpha x y)
    | (Type n,Type m) => n = m
    | _ => false


fun context_lookup (G : Ctxt) (e : Term) =
  case G of
      [] => NONE
    | (x,a)::G => if (alpha x e) then SOME a else (context_lookup G e)

fun hint_check (E : Hint) (e1 : Term) (e2 : Term) (t : Term) : bool =
  case E of
      [] => false
    | (A,x,y)::E =>
      (alpha A t andalso ((alpha x e1 andalso alpha y e2) orelse (alpha x e2 andalso alpha y e1)))
          orelse hint_check E e1 e2 t

fun Typecheck (G : Ctxt) (E : Hint) (e : Term) (t : Term) : bool =
  case (e,t) of
      (Var (x,_),tau) =>
      (case context_lookup G (Var (x,0)) of
           NONE => false
        |  SOME t' => equiv G E t t')
    | (App (e1,e2,_),tau) =>
      let val t1 = Synthesize G E e1
          val t2 = Synthesize G E e2
      in
          (case (t1,t2) of
               (SOME (Lam (_,t,m,c)), SOME (Type i)) => if Typecheck G E t (Type i) then true else false
             | (SOME (Lam (_,t,m,c)), SOME t') =>
               if equiv G E t t' then true else false
             |  _ => false)
      end
    | (Lam (x,t,m,c),Pi(y,A,B,c')) => (equiv G E t A) andalso (Typecheck (((Var (x,c)),t)::(Var (y,c'),A)::G) E m B)
    | (Pi (x,A,B,c),Type n) => Typecheck G E A (Type n) andalso Typecheck G E B (Type n)
    | (Eq _ ,Type n) => true
    | (refl(A,x,_),Eq(B,a,b,_)) => (equiv G E A B) andalso (Typecheck G E x A) andalso (equiv G E a b) andalso (equiv G E x a)
    | (Type n,Type m) => n < m
    | _ => false
and Synthesize (G : Ctxt) (E : Hint) (e : Term) : Term option =
  case e of
      Var _ => context_lookup G e
   |  Lam (x,t,n,c) =>
      let val A = beta G E t
          val B = Synthesize ((Var (x,c),A)::G) E n
      in case B of
              NONE => NONE
           |  SOME B' => SOME (Pi (x,A,B',c))
      end
   |  App (e1,e2,_) =>
      let val f = Synthesize G E e1
      in case f of
             NONE => NONE
          |  SOME f' => case beta G E f' of
                            Pi(x,A,B,_) =>
                            let val res = beta G E e2
                            in if Typecheck G E res A then SOME (beta G E (subst B x res)) else NONE end
                         | _ => NONE
      end
   |  refl (A,x,c) => SOME (Eq(beta G E A, beta G E x, beta G E x, c))
   |  Pi (x,A,B,c) =>
      let val ta = Synthesize G E A
          val tb = case ta of
                       NONE => NONE
                    |  SOME t => Synthesize ((Var (x,0),t)::G) E B
      in case (ta,tb) of
             (SOME (Type i), SOME (Type j)) =>
             if i < j then SOME (Type j) else SOME (Type i)
           | (SOME (Type i), SOME (Var _)) => ta
           | (SOME (Type _), SOME (Pi _)) => ta
           | (SOME (Type _), SOME (Eq _)) => ta
           | (SOME (Var _), SOME (Type _)) => tb
           | (SOME (Pi _), SOME (Type _)) => tb
           | (SOME (Eq _), SOME (Type _)) => tb
           | _ => NONE
      end
   |  Eq (A,x,y,c) => Synthesize G E A
   |  Type i => SOME (Type (i + 1))
and beta (G : Ctxt) (E : Hint) (e : Term) : Term =
    case e of
        Var _ => e
      | Lam _ =>  e
      | App (Lam (x,t,m,c1),e2,c) =>
        let val A = beta G E t
        in if Typecheck G E e2 A
           then beta G E (subst m x e2)
           else e
        end
      | App(e1,e2,c) => App (beta G E e1, beta G E e2, c)
      | Pi (x,A,B,c) => Pi (x, beta G E A, B, c)
      | Eq (A,x,y,c) => Eq (beta G E A, beta G E x, beta G E y, c)
      | refl (A,x,c) => refl (beta G E A, beta G E x, c)
      | Type _ => e
(** eta-congruence **)
and eta (G : Ctxt) (E : Hint) (f : Term) (e : Term) : bool =
  let val t1 = Synthesize G E f
      val t2 = Synthesize G E e
  in
      case (t1,t2) of
          (SOME A, SOME B) =>
          (if alpha A B
           then case f of
                    Lam (x,t,App (e1,Var (x',_),_),_) => x = x' andalso equiv G E e1 e
                  | _ => false
           else false)
        | _ => false
  end
(** generic equivalence procedure **)
and equiv (G : Ctxt) (E : Hint) (e1 : Term) (e2 : Term) : bool =
  let val e1 = beta G E e1
      val e2 = beta G E e2
      val t1 = Synthesize G E e1
      val t2 = Synthesize G E e2
  in
      case (t1,t2) of
          (SOME t1, SOME t2) =>
          if alpha t1 t2
          then hint_check E e1 e2 t1 orelse eta G E e1 e2 orelse alpha e1 e2
          else false
       |  _ => false
  end


fun Define (G : Ctxt) (E : Hint) (p1 : Term) (p2 : Term) : Ctxt =
  let val e1 = beta G E p1
      val e2 = beta G E p2
      val t = Synthesize G E e2
  in
      case t of
          NONE => (print "Not a type!"; G)
       |  SOME (Type i) =>
          if Typecheck G E e1 e2
          then (e1,e2)::G
          else (print "Type check failed!\n"; G)
       |  _ => (print "Not a type!\n"; G)
  end


(** naive tests **)

val ctxt = (Var ("A",0),(Type 0))::(Var ("x",0),Var ("A",0))::(Var ("Int",0),(Type 0))::nil
val hint = nil
(* reflx := refl A x : Eq A x x *)
val reflx = refl (Var ("A",0),Var ("x",0),0)
val idA = Eq (Var ("A",0),Var ("x",0),Var ("x",0),0)
(* id_int := Lam x : Int . x : Pi _ : Int . Int *)
val id_int = Lam ("x",Var ("Int",0),Var ("x",0),0)
val id_int_t = Pi ("y",Var ("Int",0),Var ("Int",0),0)
(* id_poly := Lam T : Type_0 . (Lam x : T . x) : Pi T : Type_0 . Pi _ : T . T *)
val id_poly = Lam ("T",(Type 0),Lam ("x",Var ("T",0),Var ("x",0),0),0)
val id_poly_t = Pi ("T",(Type 0),Pi ("y",Var ("T",0),Var ("T",0),0),0)

val nctxt = (Define (Define (Define ctxt hint reflx idA) hint id_int id_int_t) hint id_poly id_poly_t)

