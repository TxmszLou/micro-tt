(* constants introduction, type checking, type synthesizing *)

(* a minimal type theory *)
(**

t,u,A,B ::= x | lambda x : A . t | t u | PI (x : A) . B
         | EQ A t u | REFL A a | TYPE
with TYPE in TYPE...

*)
datatype Term = VAR of string * int | LAM of string * Term * Term * int | APP of Term * Term * int
              | PI of string * Term * Term * int | EQ of Term * Term * Term * int | REFL of Term * int
              | TYPE


type Ctxt = (Term * Term) list

fun remove a xs =
  case xs of
      [] => []
    | x::xs => if x = a then remove a xs else x :: (remove a xs)

(** collect free variables of an expression as a list **)
fun FV e =
  case e of
      VAR (x,_) => [x]
   |  LAM (x,t,e,_) => remove x (FV e @ FV t)
   |  APP (m,n,_) => FV m @ FV n
   |  PI  (x,A,B,_) => remove x (FV A @ FV B)
   |  EQ  (A,x,y,_) => FV A @ FV x @ FV y
   |  REFL (A,_) => FV A
   | TYPE => []

fun member x xs =
  case xs of
      [] => false
    | y::xs => if x = y then true else member x xs

(** invariant: **)
(** (1) each term is tupled with a number representing next free variable to be generated in the term **)
(** (2) fresh variable number of the term is always greater than that of its subterms **)
fun subst (e : Term) (x : string) (m : Term) : Term =
  case e of
      VAR (y,_) => if x = y then m else e
    | LAM (y,t,n,c) => if x = y
                       then e
                       else if member y (FV m)
                       then
                           let val nvar = "T" ^ (Int.toString c)
                           in LAM(nvar,t,(subst (subst n y (VAR (nvar,c+1))) x m),c+1)
                           end
                       else
                           LAM(y,t,(subst n x m),c)
    | APP (e1,e2,c) => APP (subst e1 x m, subst e2 x m,c)
    | PI (y,A,B,c) => if x = y
                      then e
                      else if member y (FV m)
                      then
                          let val nvar = "T" ^ (Int.toString c)
                          in PI (nvar,(subst (subst A y (VAR (nvar,c+1))) x m),
                                 (subst (subst B y (VAR (nvar,c+1))) x m),c+1)
                          end
                      else
                          PI (y,(subst A x m),(subst B x m),c)
    | EQ (A,a,b,c) => EQ (subst A x m, subst a x m, subst b x m,c)
    | REFL (A,c) => REFL (subst A x m,c)
    | TYPE => TYPE

(** alpha-congruence **)
fun alpha (s : Term) (t : Term) : bool =
  case (s,t) of
      (VAR x, VAR y) => x = y
    | (LAM(x,t,m,_), LAM(y,t',n,_)) => alpha t t' andalso alpha m (subst n y (VAR (x,0)))
    | (APP(e1,e2,_), APP(t1,t2,_)) => alpha e1 t1 andalso alpha e2 t2
    | (PI(x,A,B,_), PI(y,C,D,_)) => alpha A C andalso alpha B (subst D y (VAR (x,0)))
    | (EQ(A,a,b,_), EQ(B,x,y,_)) => alpha A B andalso alpha a x andalso alpha b y
    | (REFL(A,_), REFL(B,_)) => alpha A B
    | (TYPE, TYPE) => true
    | _ => false

fun context_lookup (G : Ctxt) (e : Term) =
  case G of
      [] => NONE
    | (x,a)::G => if alpha x e then SOME a else context_lookup G e

fun Typecheck (G : Ctxt) (e : Term) (t : Term) : bool =
  case (beta G e,beta G t) of
      (VAR(x,_), tau) =>
      (case context_lookup G (VAR (x,0)) of
          NONE => false
        | SOME t' => alpha t t')
    | (LAM(x,t,m,c), PI(y,A,B,c')) => alpha t A andalso Typecheck (((VAR (x,c)),t)::(VAR (y,c'),A)::G) m B
    | (PI _, TYPE) => true
    | (EQ _, TYPE) => true
    | (REFL(A,_), EQ(B,a,b,_)) => alpha A B andalso Typecheck G a A andalso alpha a b
    | (TYPE,TYPE) => true
    | _ => false
and beta (G : Ctxt) (e : Term) : Term =
  case e of
      VAR _ => e
   |  LAM _ => e
   |  APP (LAM (x,t,m,c1),e2,c) =>
      let val A = beta G t
      in if Typecheck G e2 A
         then beta G (subst m x e2)
         else e
      end
   |  APP(e1,e2,c) => APP (beta G e1, beta G e2, c)
   |  PI (x,A,B,c) => PI (x, beta G A, B, c)
   |  EQ (A,x,y,c) => EQ (beta G A, beta G x, beta G y, c)
   |  REFL _ => e
   |  TYPE   => e


fun Synthesize (G : Ctxt) (e : Term) : Term option =
  case e of
      VAR _ => NONE
   |  LAM (x,t,n,c) =>
      let val A = beta G t
          val B = Synthesize ((VAR (x,c),A)::G) n
      in case B of
              NONE => NONE
           |  SOME B' => SOME (PI (x,A,B',c))
      end
   |  APP (e1,e2,_) =>
      let val f = Synthesize G e1
      in case f of
             NONE => NONE
          |  SOME f' => case beta G f' of
                            PI(x,A,B,_) =>
                            let val res = beta G e2
                            in if Typecheck G res A then SOME (beta G (subst B x res)) else NONE end
                         | _ => NONE
      end
   |  REFL (A,c) => NONE
   |  PI (x,A,B,c) => SOME TYPE
   |  EQ (A,x,y,c) => SOME TYPE
   |  TYPE => SOME TYPE


fun Define (G : Ctxt) (p1 : Term) (p2 : Term) : Ctxt =
  let val e1 = beta G p1
      val e2 = beta G p2
      val t = Synthesize G e2
  in
      case t of
          NONE => (print "Not a type!"; G)
       |  SOME t1 => if alpha t1 TYPE andalso Typecheck G e1 e2
                     then (e1,e2)::G
                     else (print "Fail! You messed Up!\n"; G)
  end


val ctxt = (VAR ("A",0),TYPE)::(VAR ("x",0),VAR ("A",0))::(VAR ("Int",0),TYPE)::nil
val reflx = REFL (VAR ("A",0),0)
val idA = EQ (VAR ("A",0),VAR ("x",0),VAR ("x",0),0)
val id_int = LAM ("x",VAR ("Int",0),VAR ("x",0),0)
val id_int_t = PI ("y",VAR ("Int",0),VAR ("Int",0),0)
val id_poly = LAM ("T",TYPE,LAM ("x",VAR ("T",0),VAR ("x",0),0),0)
val id_poly_t = PI ("T",TYPE,PI ("y",VAR ("T",0),VAR ("T",0),0),0)

val nctxt = (Define (Define (Define ctxt reflx idA) id_int id_int_t) id_poly id_poly_t)
