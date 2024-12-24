Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_TRIPLE_THM_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem51407 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem51408 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem51409 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem51408 A B f) (@lem51407 A B f)). Qed.
Lemma lem51410 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem51409 A B f g). Qed.
Lemma lem51411 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem51413 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term4 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem51414 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = ((term5 _5106 _5107 P) = (term6 _5106 _5107 P)).
Proof. exact (eq_refl (term4 _5106 _5107 P)). Qed.
Lemma lem51425 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem51411 A B f g) (@lem51410 A B f g)). Qed.
Lemma lem51426 {A B C D : Type'} (f : type1198 A B C D) (g : type1198 A B C D) : (f = g) = (term7 A B C D f g).
Proof. exact (@lem51425 (type1656 A B C) D f g). Qed.
Lemma lem51427 {A B C D : Type'} (f : type1198 A B C D) : ((term8 A B C D f) = (term9 A B C D f)) = (term10 A B C D f).
Proof. exact (@lem51426 A B C D (term8 A B C D f) (term9 A B C D f)). Qed.
Lemma lem51433 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term5 _5106 _5107 P) = (term6 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51414 _5106 _5107 P) (@lem51413 _5106 _5107 P)). Qed.
Lemma lem51434 {A B C : Type'} (P : type1199 A B C) : (term11 A B C P) = (term12 A B C P).
Proof. exact (@lem51433 (prod B C) A P). Qed.
Lemma lem51435 {A B C D : Type'} (f : type1198 A B C D) : (term13 A B C D f) = (term14 A B C D f).
Proof. exact (@lem51434 A B C (term15 A B C D f)). Qed.
Lemma lem51436 {A B C D : Type'} (f : type1198 A B C D) (x : type1656 A B C) : (term16 A B C D f x) = ((term17 A B C D f x) = (term18 A B C D f x)).
Proof. exact (eq_refl (term16 A B C D f x)). Qed.
Lemma lem51437 {A B C D : Type'} (f : type1198 A B C D) : (term19 A B C D f) = (term15 A B C D f).
Proof. exact (fun_ext (fun x : type1656 A B C => @lem51436 A B C D f x)). Qed.
Lemma lem51438 {A B C : Type'} : (@all (prod A (prod B C))) = (@all (prod A (prod B C))).
Proof. exact (eq_refl (@all (prod A (prod B C)))). Qed.
Lemma lem51439 {A B C D : Type'} (f : type1198 A B C D) : (term13 A B C D f) = (term10 A B C D f).
Proof. exact (MK_COMB (@lem51438 A B C) (@lem51437 A B C D f)). Qed.
Lemma lem51440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem51441 {A B C D : Type'} (f : type1198 A B C D) : (term20 A B C D f) = (term21 A B C D f).
Proof. exact (MK_COMB (@lem51440) (@lem51439 A B C D f)). Qed.
Lemma lem51442 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p2 : prod B C) : (term22 A B C D f p1 p2) = ((term23 A B C D f p1 p2) = (term24 A B C D f p1 p2)).
Proof. exact (eq_refl (term22 A B C D f p1 p2)). Qed.
Lemma lem51443 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term25 A B C D f p1) = (term26 A B C D f p1).
Proof. exact (fun_ext (fun p2 : prod B C => @lem51442 A B C D f p1 p2)). Qed.
Lemma lem51444 {B C : Type'} : (@all (prod B C)) = (@all (prod B C)).
Proof. exact (eq_refl (@all (prod B C))). Qed.
Lemma lem51445 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term27 A B C D f p1) = (term28 A B C D f p1).
Proof. exact (MK_COMB (@lem51444 B C) (@lem51443 A B C D f p1)). Qed.
Lemma lem51446 {A B C D : Type'} (f : type1198 A B C D) : (term29 A B C D f) = (term30 A B C D f).
Proof. exact (fun_ext (fun p1 : A => @lem51445 A B C D f p1)). Qed.
Lemma lem51447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51448 {A B C D : Type'} (f : type1198 A B C D) : (term14 A B C D f) = (term31 A B C D f).
Proof. exact (MK_COMB (@lem51447 A) (@lem51446 A B C D f)). Qed.
Lemma lem51449 {A B C D : Type'} (f : type1198 A B C D) : ((term13 A B C D f) = (term14 A B C D f)) = ((term10 A B C D f) = (term31 A B C D f)).
Proof. exact (MK_COMB (@lem51441 A B C D f) (@lem51448 A B C D f)). Qed.
Lemma lem51450 {A B C D : Type'} (f : type1198 A B C D) : (term10 A B C D f) = (term31 A B C D f).
Proof. exact (EQ_MP (@lem51449 A B C D f) (@lem51435 A B C D f)). Qed.
Lemma lem51457 {A B C D : Type'} (f : type1198 A B C D) : ((term8 A B C D f) = (term9 A B C D f)) = (term31 A B C D f).
Proof. exact (TRANS (@lem51427 A B C D f) (@lem51450 A B C D f)). Qed.
Lemma lem51463 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term5 _5106 _5107 P) = (term6 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51414 _5106 _5107 P) (@lem51413 _5106 _5107 P)). Qed.
Lemma lem51464 {B C : Type'} (P : type1210 B C) : (term32 B C P) = (term33 B C P).
Proof. exact (@lem51463 C B P). Qed.
Lemma lem51465 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term34 A B C D f p1) = (term35 A B C D f p1).
Proof. exact (@lem51464 B C (term26 A B C D f p1)). Qed.
Lemma lem51466 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p2 : prod B C) : (term36 A B C D f p1 p2) = ((term23 A B C D f p1 p2) = (term24 A B C D f p1 p2)).
Proof. exact (eq_refl (term36 A B C D f p1 p2)). Qed.
Lemma lem51467 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term37 A B C D f p1) = (term26 A B C D f p1).
Proof. exact (fun_ext (fun p2 : prod B C => @lem51466 A B C D f p1 p2)). Qed.
Lemma lem51468 {B C : Type'} : (@all (prod B C)) = (@all (prod B C)).
Proof. exact (eq_refl (@all (prod B C))). Qed.
Lemma lem51469 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term34 A B C D f p1) = (term28 A B C D f p1).
Proof. exact (MK_COMB (@lem51468 B C) (@lem51467 A B C D f p1)). Qed.
Lemma lem51470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem51471 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term38 A B C D f p1) = (term39 A B C D f p1).
Proof. exact (MK_COMB (@lem51470) (@lem51469 A B C D f p1)). Qed.
Lemma lem51472 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : (term40 A B C D f p1 p1' p2) = ((term41 A B C D f p1 p1' p2) = (term42 A B C D f p1 p1' p2)).
Proof. exact (eq_refl (term40 A B C D f p1 p1' p2)). Qed.
Lemma lem51473 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) : (term43 A B C D f p1 p1') = (term44 A B C D f p1 p1').
Proof. exact (fun_ext (fun p2 : C => @lem51472 A B C D f p1 p1' p2)). Qed.
Lemma lem51474 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem51475 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) : (term45 A B C D f p1 p1') = (term46 A B C D f p1 p1').
Proof. exact (MK_COMB (@lem51474 C) (@lem51473 A B C D f p1 p1')). Qed.
Lemma lem51476 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term47 A B C D f p1) = (term48 A B C D f p1).
Proof. exact (fun_ext (fun p1' : B => @lem51475 A B C D f p1 p1')). Qed.
Lemma lem51477 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51478 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term35 A B C D f p1) = (term49 A B C D f p1).
Proof. exact (MK_COMB (@lem51477 B) (@lem51476 A B C D f p1)). Qed.
Lemma lem51479 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : ((term34 A B C D f p1) = (term35 A B C D f p1)) = ((term28 A B C D f p1) = (term49 A B C D f p1)).
Proof. exact (MK_COMB (@lem51471 A B C D f p1) (@lem51478 A B C D f p1)). Qed.
Lemma lem51480 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term28 A B C D f p1) = (term49 A B C D f p1).
Proof. exact (EQ_MP (@lem51479 A B C D f p1) (@lem51465 A B C D f p1)). Qed.
Lemma lem51498 {A B : Type'} (f : A -> B) (y : A) : (term50 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem51499 {A B C D : Type'} (f : type1198 A B C D) (y : type1656 A B C) : (term17 A B C D f y) = (f y).
Proof. exact (@lem51498 (type1656 A B C) D f y). Qed.
Lemma lem51500 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : (term41 A B C D f p1 p1' p2) = (term51 A B C D f p1 p1' p2).
Proof. exact (@lem51499 A B C D f (term52 A B C p1 p1' p2)). Qed.
Lemma lem51501 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem51502 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : (term53 A B C D f p1 p1' p2) = (term54 A B C D f p1 p1' p2).
Proof. exact (MK_COMB (@lem51501 D) (@lem51500 A B C D f p1 p1' p2)). Qed.
Lemma lem51503 {A B C : Type'} (a0 : A) (a1 : prod B C) : a0 = (term55 A B C a0 a1).
Proof. exact (@lem51128 A (prod B C) a0 a1). Qed.
Lemma lem51504 {A B C : Type'} (x : A) (y : B) (z : C) : x = (term56 A B C x y z).
Proof. exact (@lem51503 A B C x (@pair B C y z)). Qed.
Lemma lem51505 {A B C : Type'} (a0 : A) (a1 : prod B C) : a1 = (term57 A B C a0 a1).
Proof. exact (@lem51159 A (prod B C) a0 a1). Qed.
Lemma lem51506 {A B C : Type'} (x : A) (y : B) (z : C) : (@pair B C y z) = (term58 A B C x y z).
Proof. exact (@lem51505 A B C x (@pair B C y z)). Qed.
Lemma lem51507 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem51508 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (eq_refl (term59 A)). Qed.
Lemma lem51509 {A B C : Type'} (x : A) (y : B) (z : C) : (term60 A x) = (term61 A B C x y z).
Proof. exact (MK_COMB (@lem51508 A) (@lem51504 A B C x y z)). Qed.
Lemma lem51510 {A B C : Type'} (x : A) (y : B) (z : C) : (term61 A B C x y z) = (term56 A B C x y z).
Proof. exact (eq_refl (term61 A B C x y z)). Qed.
Lemma lem51511 {A : Type'} (x : A) : (term62 A x) = (term62 A x).
Proof. exact (eq_refl (term62 A x)). Qed.
Lemma lem51512 {A B C : Type'} (x : A) (y : B) (z : C) : ((term60 A x) = (term61 A B C x y z)) = ((term60 A x) = (term56 A B C x y z)).
Proof. exact (MK_COMB (@lem51511 A x) (@lem51510 A B C x y z)). Qed.
Lemma lem51513 {A : Type'} (x : A) : (term60 A x) = x.
Proof. exact (eq_refl (term60 A x)). Qed.
Lemma lem51514 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem51515 {A : Type'} (x : A) : (term62 A x) = (@eq A x).
Proof. exact (MK_COMB (@lem51514 A) (@lem51513 A x)). Qed.
Lemma lem51516 {A B C : Type'} (x : A) (y : B) (z : C) : (term56 A B C x y z) = (term56 A B C x y z).
Proof. exact (eq_refl (term56 A B C x y z)). Qed.
Lemma lem51517 {A B C : Type'} (x : A) (y : B) (z : C) : ((term60 A x) = (term56 A B C x y z)) = (x = (term56 A B C x y z)).
Proof. exact (MK_COMB (@lem51515 A x) (@lem51516 A B C x y z)). Qed.
Lemma lem51518 {A B C : Type'} (x : A) (y : B) (z : C) : ((term60 A x) = (term61 A B C x y z)) = (x = (term56 A B C x y z)).
Proof. exact (TRANS (@lem51512 A B C x y z) (@lem51517 A B C x y z)). Qed.
Lemma lem51519 {A B C : Type'} (x : A) (y : B) (z : C) : x = (term56 A B C x y z).
Proof. exact (EQ_MP (@lem51518 A B C x y z) (@lem51509 A B C x y z)). Qed.
Lemma lem51520 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem51521 {A B C : Type'} (x : A) (y : B) (z : C) : (x = x) = (x = (term56 A B C x y z)).
Proof. exact (MK_COMB (@lem51520 A x) (@lem51519 A B C x y z)). Qed.
Lemma lem51522 {A B C : Type'} (x : A) (y : B) (z : C) : x = (term56 A B C x y z).
Proof. exact (EQ_MP (@lem51521 A B C x y z) (@lem51507 A x)). Qed.
Lemma lem51523 {B C : Type'} (a0 : B) (a1 : C) : a0 = (term63 B C a0 a1).
Proof. exact (@lem51128 B C a0 a1). Qed.
Lemma lem51524 {B C : Type'} (y : B) (z : C) : y = (term63 B C y z).
Proof. exact (@lem51523 B C y z). Qed.
Lemma lem51525 {B C : Type'} (a0 : B) (a1 : C) : a1 = (term64 B C a0 a1).
Proof. exact (@lem51159 B C a0 a1). Qed.
Lemma lem51526 {B C : Type'} (y : B) (z : C) : z = (term64 B C y z).
Proof. exact (@lem51525 B C y z). Qed.
Lemma lem51527 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem51528 {B : Type'} : (term59 B) = (term59 B).
Proof. exact (eq_refl (term59 B)). Qed.
Lemma lem51529 {B C : Type'} (y : B) (z : C) : (term60 B y) = (term65 B C y z).
Proof. exact (MK_COMB (@lem51528 B) (@lem51524 B C y z)). Qed.
Lemma lem51530 {B C : Type'} (y : B) (z : C) : (term65 B C y z) = (term63 B C y z).
Proof. exact (eq_refl (term65 B C y z)). Qed.
Lemma lem51531 {B : Type'} (y : B) : (term62 B y) = (term62 B y).
Proof. exact (eq_refl (term62 B y)). Qed.
Lemma lem51532 {B C : Type'} (y : B) (z : C) : ((term60 B y) = (term65 B C y z)) = ((term60 B y) = (term63 B C y z)).
Proof. exact (MK_COMB (@lem51531 B y) (@lem51530 B C y z)). Qed.
Lemma lem51533 {B : Type'} (y : B) : (term60 B y) = y.
Proof. exact (eq_refl (term60 B y)). Qed.
Lemma lem51534 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem51535 {B : Type'} (y : B) : (term62 B y) = (@eq B y).
Proof. exact (MK_COMB (@lem51534 B) (@lem51533 B y)). Qed.
Lemma lem51536 {B C : Type'} (y : B) (z : C) : (term63 B C y z) = (term63 B C y z).
Proof. exact (eq_refl (term63 B C y z)). Qed.
Lemma lem51537 {B C : Type'} (y : B) (z : C) : ((term60 B y) = (term63 B C y z)) = (y = (term63 B C y z)).
Proof. exact (MK_COMB (@lem51535 B y) (@lem51536 B C y z)). Qed.
Lemma lem51538 {B C : Type'} (y : B) (z : C) : ((term60 B y) = (term65 B C y z)) = (y = (term63 B C y z)).
Proof. exact (TRANS (@lem51532 B C y z) (@lem51537 B C y z)). Qed.
Lemma lem51539 {B C : Type'} (y : B) (z : C) : y = (term63 B C y z).
Proof. exact (EQ_MP (@lem51538 B C y z) (@lem51529 B C y z)). Qed.
Lemma lem51540 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem51541 {B C : Type'} (y : B) (z : C) : (y = y) = (y = (term63 B C y z)).
Proof. exact (MK_COMB (@lem51540 B y) (@lem51539 B C y z)). Qed.
Lemma lem51542 {B C : Type'} (y : B) (z : C) : y = (term63 B C y z).
Proof. exact (EQ_MP (@lem51541 B C y z) (@lem51527 B y)). Qed.
Lemma lem51543 {C : Type'} (z : C) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem51544 {C : Type'} : (term59 C) = (term59 C).
Proof. exact (eq_refl (term59 C)). Qed.
Lemma lem51545 {B C : Type'} (y : B) (z : C) : (term60 C z) = (term66 B C y z).
Proof. exact (MK_COMB (@lem51544 C) (@lem51526 B C y z)). Qed.
Lemma lem51546 {B C : Type'} (y : B) (z : C) : (term66 B C y z) = (term64 B C y z).
Proof. exact (eq_refl (term66 B C y z)). Qed.
Lemma lem51547 {C : Type'} (z : C) : (term62 C z) = (term62 C z).
Proof. exact (eq_refl (term62 C z)). Qed.
Lemma lem51548 {B C : Type'} (y : B) (z : C) : ((term60 C z) = (term66 B C y z)) = ((term60 C z) = (term64 B C y z)).
Proof. exact (MK_COMB (@lem51547 C z) (@lem51546 B C y z)). Qed.
Lemma lem51549 {C : Type'} (z : C) : (term60 C z) = z.
Proof. exact (eq_refl (term60 C z)). Qed.
Lemma lem51550 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem51551 {C : Type'} (z : C) : (term62 C z) = (@eq C z).
Proof. exact (MK_COMB (@lem51550 C) (@lem51549 C z)). Qed.
Lemma lem51552 {B C : Type'} (y : B) (z : C) : (term64 B C y z) = (term64 B C y z).
Proof. exact (eq_refl (term64 B C y z)). Qed.
Lemma lem51553 {B C : Type'} (y : B) (z : C) : ((term60 C z) = (term64 B C y z)) = (z = (term64 B C y z)).
Proof. exact (MK_COMB (@lem51551 C z) (@lem51552 B C y z)). Qed.
Lemma lem51554 {B C : Type'} (y : B) (z : C) : ((term60 C z) = (term66 B C y z)) = (z = (term64 B C y z)).
Proof. exact (TRANS (@lem51548 B C y z) (@lem51553 B C y z)). Qed.
Lemma lem51555 {B C : Type'} (y : B) (z : C) : z = (term64 B C y z).
Proof. exact (EQ_MP (@lem51554 B C y z) (@lem51545 B C y z)). Qed.
Lemma lem51556 {C : Type'} (z : C) : (@eq C z) = (@eq C z).
Proof. exact (eq_refl (@eq C z)). Qed.
Lemma lem51557 {B C : Type'} (y : B) (z : C) : (z = z) = (z = (term64 B C y z)).
Proof. exact (MK_COMB (@lem51556 C z) (@lem51555 B C y z)). Qed.
Lemma lem51558 {B C : Type'} (y : B) (z : C) : z = (term64 B C y z).
Proof. exact (EQ_MP (@lem51557 B C y z) (@lem51543 C z)). Qed.
Lemma lem51559 {B C : Type'} : (term67 B C) = (term67 B C).
Proof. exact (eq_refl (term67 B C)). Qed.
Lemma lem51560 {A B C : Type'} (x : A) (y : B) (z : C) : (term68 B C y z) = (term69 A B C x y z).
Proof. exact (MK_COMB (@lem51559 B C) (@lem51506 A B C x y z)). Qed.
Lemma lem51561 {A B C : Type'} (x : A) (y : B) (z : C) : (term69 A B C x y z) = (term70 A B C x y z).
Proof. exact (eq_refl (term69 A B C x y z)). Qed.
Lemma lem51562 {B C : Type'} (y : B) (z : C) : (term71 B C y z) = (term71 B C y z).
Proof. exact (eq_refl (term71 B C y z)). Qed.
Lemma lem51563 {A B C : Type'} (x : A) (y : B) (z : C) : ((term68 B C y z) = (term69 A B C x y z)) = ((term68 B C y z) = (term70 A B C x y z)).
Proof. exact (MK_COMB (@lem51562 B C y z) (@lem51561 A B C x y z)). Qed.
Lemma lem51564 {B C : Type'} (y : B) (z : C) : (term68 B C y z) = (term63 B C y z).
Proof. exact (eq_refl (term68 B C y z)). Qed.
Lemma lem51565 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem51566 {B C : Type'} (y : B) (z : C) : (term71 B C y z) = (term72 B C y z).
Proof. exact (MK_COMB (@lem51565 B) (@lem51564 B C y z)). Qed.
Lemma lem51567 {A B C : Type'} (x : A) (y : B) (z : C) : (term70 A B C x y z) = (term70 A B C x y z).
Proof. exact (eq_refl (term70 A B C x y z)). Qed.
Lemma lem51568 {A B C : Type'} (x : A) (y : B) (z : C) : ((term68 B C y z) = (term70 A B C x y z)) = ((term63 B C y z) = (term70 A B C x y z)).
Proof. exact (MK_COMB (@lem51566 B C y z) (@lem51567 A B C x y z)). Qed.
Lemma lem51569 {A B C : Type'} (x : A) (y : B) (z : C) : ((term68 B C y z) = (term69 A B C x y z)) = ((term63 B C y z) = (term70 A B C x y z)).
Proof. exact (TRANS (@lem51563 A B C x y z) (@lem51568 A B C x y z)). Qed.
Lemma lem51570 {A B C : Type'} (x : A) (y : B) (z : C) : (term63 B C y z) = (term70 A B C x y z).
Proof. exact (EQ_MP (@lem51569 A B C x y z) (@lem51560 A B C x y z)). Qed.
Lemma lem51571 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem51572 {A B C : Type'} (x : A) (y : B) (z : C) : (y = (term63 B C y z)) = (y = (term70 A B C x y z)).
Proof. exact (MK_COMB (@lem51571 B y) (@lem51570 A B C x y z)). Qed.
Lemma lem51573 {A B C : Type'} (x : A) (y : B) (z : C) : y = (term70 A B C x y z).
Proof. exact (EQ_MP (@lem51572 A B C x y z) (@lem51542 B C y z)). Qed.
Lemma lem51574 {B C : Type'} : (term73 B C) = (term73 B C).
Proof. exact (eq_refl (term73 B C)). Qed.
Lemma lem51575 {A B C : Type'} (x : A) (y : B) (z : C) : (term74 B C y z) = (term75 A B C x y z).
Proof. exact (MK_COMB (@lem51574 B C) (@lem51506 A B C x y z)). Qed.
Lemma lem51576 {A B C : Type'} (x : A) (y : B) (z : C) : (term75 A B C x y z) = (term76 A B C x y z).
Proof. exact (eq_refl (term75 A B C x y z)). Qed.
Lemma lem51577 {B C : Type'} (y : B) (z : C) : (term77 B C y z) = (term77 B C y z).
Proof. exact (eq_refl (term77 B C y z)). Qed.
Lemma lem51578 {A B C : Type'} (x : A) (y : B) (z : C) : ((term74 B C y z) = (term75 A B C x y z)) = ((term74 B C y z) = (term76 A B C x y z)).
Proof. exact (MK_COMB (@lem51577 B C y z) (@lem51576 A B C x y z)). Qed.
Lemma lem51579 {B C : Type'} (y : B) (z : C) : (term74 B C y z) = (term64 B C y z).
Proof. exact (eq_refl (term74 B C y z)). Qed.
Lemma lem51580 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem51581 {B C : Type'} (y : B) (z : C) : (term77 B C y z) = (term78 B C y z).
Proof. exact (MK_COMB (@lem51580 C) (@lem51579 B C y z)). Qed.
Lemma lem51582 {A B C : Type'} (x : A) (y : B) (z : C) : (term76 A B C x y z) = (term76 A B C x y z).
Proof. exact (eq_refl (term76 A B C x y z)). Qed.
Lemma lem51583 {A B C : Type'} (x : A) (y : B) (z : C) : ((term74 B C y z) = (term76 A B C x y z)) = ((term64 B C y z) = (term76 A B C x y z)).
Proof. exact (MK_COMB (@lem51581 B C y z) (@lem51582 A B C x y z)). Qed.
Lemma lem51584 {A B C : Type'} (x : A) (y : B) (z : C) : ((term74 B C y z) = (term75 A B C x y z)) = ((term64 B C y z) = (term76 A B C x y z)).
Proof. exact (TRANS (@lem51578 A B C x y z) (@lem51583 A B C x y z)). Qed.
Lemma lem51585 {A B C : Type'} (x : A) (y : B) (z : C) : (term64 B C y z) = (term76 A B C x y z).
Proof. exact (EQ_MP (@lem51584 A B C x y z) (@lem51575 A B C x y z)). Qed.
Lemma lem51586 {C : Type'} (z : C) : (@eq C z) = (@eq C z).
Proof. exact (eq_refl (@eq C z)). Qed.
Lemma lem51587 {A B C : Type'} (x : A) (y : B) (z : C) : (z = (term64 B C y z)) = (z = (term76 A B C x y z)).
Proof. exact (MK_COMB (@lem51586 C z) (@lem51585 A B C x y z)). Qed.
Lemma lem51588 {A B C : Type'} (x : A) (y : B) (z : C) : z = (term76 A B C x y z).
Proof. exact (EQ_MP (@lem51587 A B C x y z) (@lem51558 B C y z)). Qed.
Lemma lem51589 {A B C D : Type'} (f : type1198 A B C D) : (term79 A B C D f) = (term79 A B C D f).
Proof. exact (eq_refl (term79 A B C D f)). Qed.
Lemma lem51590 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term80 A B C D f x) = (term81 A B C D f x y z).
Proof. exact (MK_COMB (@lem51589 A B C D f) (@lem51522 A B C x y z)). Qed.
Lemma lem51591 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term81 A B C D f x y z) = (term82 A B C D f x y z).
Proof. exact (eq_refl (term81 A B C D f x y z)). Qed.
Lemma lem51592 {A B C D : Type'} (f : type1198 A B C D) (x : A) : (term83 A B C D f x) = (term83 A B C D f x).
Proof. exact (eq_refl (term83 A B C D f x)). Qed.
Lemma lem51593 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term80 A B C D f x) = (term81 A B C D f x y z)) = ((term80 A B C D f x) = (term82 A B C D f x y z)).
Proof. exact (MK_COMB (@lem51592 A B C D f x) (@lem51591 A B C D f x y z)). Qed.
Lemma lem51594 {A B C D : Type'} (f : type1198 A B C D) (x : A) : (term80 A B C D f x) = (term84 A B C D f x).
Proof. exact (eq_refl (term80 A B C D f x)). Qed.
Lemma lem51595 {B C D : Type'} : (@eq (B -> C -> D)) = (@eq (B -> C -> D)).
Proof. exact (eq_refl (@eq (B -> C -> D))). Qed.
Lemma lem51596 {A B C D : Type'} (f : type1198 A B C D) (x : A) : (term83 A B C D f x) = (term85 A B C D f x).
Proof. exact (MK_COMB (@lem51595 B C D) (@lem51594 A B C D f x)). Qed.
Lemma lem51597 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term82 A B C D f x y z) = (term82 A B C D f x y z).
Proof. exact (eq_refl (term82 A B C D f x y z)). Qed.
Lemma lem51598 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term80 A B C D f x) = (term82 A B C D f x y z)) = ((term84 A B C D f x) = (term82 A B C D f x y z)).
Proof. exact (MK_COMB (@lem51596 A B C D f x) (@lem51597 A B C D f x y z)). Qed.
Lemma lem51599 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term80 A B C D f x) = (term81 A B C D f x y z)) = ((term84 A B C D f x) = (term82 A B C D f x y z)).
Proof. exact (TRANS (@lem51593 A B C D f x y z) (@lem51598 A B C D f x y z)). Qed.
Lemma lem51600 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term84 A B C D f x) = (term82 A B C D f x y z).
Proof. exact (EQ_MP (@lem51599 A B C D f x y z) (@lem51590 A B C D f x y z)). Qed.
Lemma lem51601 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term86 A B C D f x y) = (term87 A B C D f x y z).
Proof. exact (MK_COMB (@lem51600 A B C D f x y z) (@lem51573 A B C x y z)). Qed.
Lemma lem51602 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term87 A B C D f x y z) = (term88 A B C D f x y z).
Proof. exact (eq_refl (term87 A B C D f x y z)). Qed.
Lemma lem51603 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : (term89 A B C D f x y) = (term89 A B C D f x y).
Proof. exact (eq_refl (term89 A B C D f x y)). Qed.
Lemma lem51604 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term86 A B C D f x y) = (term87 A B C D f x y z)) = ((term86 A B C D f x y) = (term88 A B C D f x y z)).
Proof. exact (MK_COMB (@lem51603 A B C D f x y) (@lem51602 A B C D f x y z)). Qed.
Lemma lem51605 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : (term86 A B C D f x y) = (term90 A B C D f x y).
Proof. exact (eq_refl (term86 A B C D f x y)). Qed.
Lemma lem51606 {C D : Type'} : (@eq (C -> D)) = (@eq (C -> D)).
Proof. exact (eq_refl (@eq (C -> D))). Qed.
Lemma lem51607 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : (term89 A B C D f x y) = (term91 A B C D f x y).
Proof. exact (MK_COMB (@lem51606 C D) (@lem51605 A B C D f x y)). Qed.
Lemma lem51608 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term88 A B C D f x y z) = (term88 A B C D f x y z).
Proof. exact (eq_refl (term88 A B C D f x y z)). Qed.
Lemma lem51609 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term86 A B C D f x y) = (term88 A B C D f x y z)) = ((term90 A B C D f x y) = (term88 A B C D f x y z)).
Proof. exact (MK_COMB (@lem51607 A B C D f x y) (@lem51608 A B C D f x y z)). Qed.
Lemma lem51610 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term86 A B C D f x y) = (term87 A B C D f x y z)) = ((term90 A B C D f x y) = (term88 A B C D f x y z)).
Proof. exact (TRANS (@lem51604 A B C D f x y z) (@lem51609 A B C D f x y z)). Qed.
Lemma lem51611 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term90 A B C D f x y) = (term88 A B C D f x y z).
Proof. exact (EQ_MP (@lem51610 A B C D f x y z) (@lem51601 A B C D f x y z)). Qed.
Lemma lem51612 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term92 A B C D f x y z) = (term93 A B C D f x y z).
Proof. exact (MK_COMB (@lem51611 A B C D f x y z) (@lem51588 A B C x y z)). Qed.
Lemma lem51613 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term93 A B C D f x y z) = (term94 A B C D f x y z).
Proof. exact (eq_refl (term93 A B C D f x y z)). Qed.
Lemma lem51614 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term95 A B C D f x y z) = (term95 A B C D f x y z).
Proof. exact (eq_refl (term95 A B C D f x y z)). Qed.
Lemma lem51615 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term92 A B C D f x y z) = (term93 A B C D f x y z)) = ((term92 A B C D f x y z) = (term94 A B C D f x y z)).
Proof. exact (MK_COMB (@lem51614 A B C D f x y z) (@lem51613 A B C D f x y z)). Qed.
Lemma lem51616 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term92 A B C D f x y z) = (term51 A B C D f x y z).
Proof. exact (eq_refl (term92 A B C D f x y z)). Qed.
Lemma lem51617 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem51618 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term95 A B C D f x y z) = (term54 A B C D f x y z).
Proof. exact (MK_COMB (@lem51617 D) (@lem51616 A B C D f x y z)). Qed.
Lemma lem51619 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term94 A B C D f x y z) = (term94 A B C D f x y z).
Proof. exact (eq_refl (term94 A B C D f x y z)). Qed.
Lemma lem51620 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term92 A B C D f x y z) = (term94 A B C D f x y z)) = ((term51 A B C D f x y z) = (term94 A B C D f x y z)).
Proof. exact (MK_COMB (@lem51618 A B C D f x y z) (@lem51619 A B C D f x y z)). Qed.
Lemma lem51621 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term92 A B C D f x y z) = (term93 A B C D f x y z)) = ((term51 A B C D f x y z) = (term94 A B C D f x y z)).
Proof. exact (TRANS (@lem51615 A B C D f x y z) (@lem51620 A B C D f x y z)). Qed.
Lemma lem51622 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term51 A B C D f x y z) = (term94 A B C D f x y z).
Proof. exact (EQ_MP (@lem51621 A B C D f x y z) (@lem51612 A B C D f x y z)). Qed.
Lemma lem51623 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term94 A B C D f x y z) = (term51 A B C D f x y z).
Proof. exact (SYM (@lem51622 A B C D f x y z)). Qed.
Lemma lem51624 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term96 A B C D f x y z) = (term94 A B C D f x y z).
Proof. exact (eq_refl (term96 A B C D f x y z)). Qed.
Lemma lem51625 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term96 A B C D f x y z) = (term51 A B C D f x y z).
Proof. exact (TRANS (@lem51624 A B C D f x y z) (@lem51623 A B C D f x y z)). Qed.
Lemma lem51626 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : term97 A B C D f x y.
Proof. exact (fun z : C => @lem51625 A B C D f x y z). Qed.
Lemma lem51627 {A B C D : Type'} (f : type1198 A B C D) (x : A) : term98 A B C D f x.
Proof. exact (fun y : B => @lem51626 A B C D f x y). Qed.
Lemma lem51628 {A B C D : Type'} (f : type1198 A B C D) : term99 A B C D f.
Proof. exact (fun x : A => @lem51627 A B C D f x). Qed.
Lemma lem51629 {A B C D : Type'} (f : type1198 A B C D) : term100 A B C D f.
Proof. exact (ex_intro (term101 A B C D f) (term102 A B C D f) (@lem51628 A B C D f)). Qed.
Lemma lem51631 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem51632 {D : Type'} (a : D) (b : D) : (a = b) = (@GEQ D a b).
Proof. exact (@lem51631 D a b). Qed.
Lemma lem51633 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) (x : A) (y : B) (z : C) : ((term51 A B C D _1424 x y z) = (term51 A B C D f x y z)) = (term103 A B C D _1424 f x y z).
Proof. exact (@lem51632 D (term51 A B C D _1424 x y z) (term51 A B C D f x y z)). Qed.
Lemma lem51634 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) (x : A) (y : B) : (term104 A B C D _1424 f x y) = (term105 A B C D _1424 f x y).
Proof. exact (fun_ext (fun z : C => @lem51633 A B C D _1424 f x y z)). Qed.
Lemma lem51635 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem51636 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) (x : A) (y : B) : (term106 A B C D _1424 f x y) = (term107 A B C D _1424 f x y).
Proof. exact (MK_COMB (@lem51635 C) (@lem51634 A B C D _1424 f x y)). Qed.
Lemma lem51637 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) (x : A) : (term108 A B C D _1424 f x) = (term109 A B C D _1424 f x).
Proof. exact (fun_ext (fun y : B => @lem51636 A B C D _1424 f x y)). Qed.
Lemma lem51638 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51639 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) (x : A) : (term110 A B C D _1424 f x) = (term111 A B C D _1424 f x).
Proof. exact (MK_COMB (@lem51638 B) (@lem51637 A B C D _1424 f x)). Qed.
Lemma lem51640 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) : (term112 A B C D _1424 f) = (term113 A B C D _1424 f).
Proof. exact (fun_ext (fun x : A => @lem51639 A B C D _1424 f x)). Qed.
Lemma lem51641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51642 {A B C D : Type'} (_1424 : type1198 A B C D) (f : type1198 A B C D) : (term114 A B C D _1424 f) = (term115 A B C D _1424 f).
Proof. exact (MK_COMB (@lem51641 A) (@lem51640 A B C D _1424 f)). Qed.
Lemma lem51643 {A B C D : Type'} (f : type1198 A B C D) : (term101 A B C D f) = (term116 A B C D f).
Proof. exact (fun_ext (fun _1424 : type1198 A B C D => @lem51642 A B C D _1424 f)). Qed.
Lemma lem51644 {A B C D : Type'} : (@ex ((prod A (prod B C)) -> D)) = (@ex ((prod A (prod B C)) -> D)).
Proof. exact (eq_refl (@ex ((prod A (prod B C)) -> D))). Qed.
Lemma lem51645 {A B C D : Type'} (f : type1198 A B C D) : (term100 A B C D f) = (term117 A B C D f).
Proof. exact (MK_COMB (@lem51644 A B C D) (@lem51643 A B C D f)). Qed.
Lemma lem51646 {A B C D : Type'} (f : type1198 A B C D) : term117 A B C D f.
Proof. exact (EQ_MP (@lem51645 A B C D f) (@lem51629 A B C D f)). Qed.
Lemma lem51648 {_5076 : Type'} (P : _5076 -> Prop) : term118 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem51649 {A B C D : Type'} (P : type314 A B C D) : term119 A B C D P.
Proof. exact (@lem51648 (type1198 A B C D) P). Qed.
Lemma lem51650 {A B C D : Type'} (f : type1198 A B C D) : term120 A B C D f.
Proof. exact (@lem51649 A B C D (term116 A B C D f)). Qed.
Lemma lem51651 {A B C D : Type'} (f : type1198 A B C D) : term121 A B C D f.
Proof. exact (@lem51650 A B C D f (@lem51646 A B C D f)). Qed.
Lemma lem51652 {A B C D : Type'} (f : type1198 A B C D) : (term121 A B C D f) = (term122 A B C D f).
Proof. exact (eq_refl (term121 A B C D f)). Qed.
Lemma lem51653 {A B C D : Type'} (f : type1198 A B C D) : term122 A B C D f.
Proof. exact (EQ_MP (@lem51652 A B C D f) (@lem51651 A B C D f)). Qed.
Lemma lem51654 {A B C D : Type'} (f : type1198 A B C D) (x : A) : term123 A B C D f x.
Proof. exact (@lem51653 A B C D f x). Qed.
Lemma lem51655 {A B C D : Type'} (f : type1198 A B C D) (x : A) : (term123 A B C D f x) = (term124 A B C D f x).
Proof. exact (eq_refl (term123 A B C D f x)). Qed.
Lemma lem51656 {A B C D : Type'} (f : type1198 A B C D) (x : A) : term124 A B C D f x.
Proof. exact (EQ_MP (@lem51655 A B C D f x) (@lem51654 A B C D f x)). Qed.
Lemma lem51657 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : term125 A B C D f x y.
Proof. exact (@lem51656 A B C D f x y). Qed.
Lemma lem51658 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : (term125 A B C D f x y) = (term126 A B C D f x y).
Proof. exact (eq_refl (term125 A B C D f x y)). Qed.
Lemma lem51659 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) : term126 A B C D f x y.
Proof. exact (EQ_MP (@lem51658 A B C D f x y) (@lem51657 A B C D f x y)). Qed.
Lemma lem51660 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : term127 A B C D f x y z.
Proof. exact (@lem51659 A B C D f x y z). Qed.
Lemma lem51661 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term127 A B C D f x y z) = (term128 A B C D f x y z).
Proof. exact (eq_refl (term127 A B C D f x y z)). Qed.
Lemma lem51662 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : term128 A B C D f x y z.
Proof. exact (EQ_MP (@lem51661 A B C D f x y z) (@lem51660 A B C D f x y z)). Qed.
Lemma lem51664 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem51665 {D : Type'} (a : D) (b : D) : (@GEQ D a b) = (a = b).
Proof. exact (@lem51664 D a b). Qed.
Lemma lem51666 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term128 A B C D f x y z) = ((term42 A B C D f x y z) = (term51 A B C D f x y z)).
Proof. exact (@lem51665 D (term42 A B C D f x y z) (term51 A B C D f x y z)). Qed.
Lemma lem51667 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term42 A B C D f x y z) = (term51 A B C D f x y z).
Proof. exact (EQ_MP (@lem51666 A B C D f x y z) (@lem51662 A B C D f x y z)). Qed.
Lemma lem51668 {A B C D : Type'} (f : type1198 A B C D) (x : A) (y : B) (z : C) : (term42 A B C D f x y z) = (term51 A B C D f x y z).
Proof. exact (@lem51667 A B C D f x y z). Qed.
Lemma lem51669 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : (term42 A B C D f p1 p1' p2) = (term51 A B C D f p1 p1' p2).
Proof. exact (@lem51668 A B C D f p1 p1' p2). Qed.
Lemma lem51670 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : ((term41 A B C D f p1 p1' p2) = (term42 A B C D f p1 p1' p2)) = ((term51 A B C D f p1 p1' p2) = (term51 A B C D f p1 p1' p2)).
Proof. exact (MK_COMB (@lem51502 A B C D f p1 p1' p2) (@lem51669 A B C D f p1 p1' p2)). Qed.
Lemma lem51672 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem51673 {D : Type'} (x : D) : (x = x) = True.
Proof. exact (@lem51672 D x). Qed.
Lemma lem51674 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : ((term51 A B C D f p1 p1' p2) = (term51 A B C D f p1 p1' p2)) = True.
Proof. exact (@lem51673 D (term51 A B C D f p1 p1' p2)). Qed.
Lemma lem51675 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) (p2 : C) : ((term41 A B C D f p1 p1' p2) = (term42 A B C D f p1 p1' p2)) = True.
Proof. exact (TRANS (@lem51670 A B C D f p1 p1' p2) (@lem51674 A B C D f p1 p1' p2)). Qed.
Lemma lem51676 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) : (term44 A B C D f p1 p1') = (term129 C).
Proof. exact (fun_ext (fun p2 : C => @lem51675 A B C D f p1 p1' p2)). Qed.
Lemma lem51677 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem51678 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) : (term46 A B C D f p1 p1') = (term130 C).
Proof. exact (MK_COMB (@lem51677 C) (@lem51676 A B C D f p1 p1')). Qed.
Lemma lem51680 {A : Type'} (t : Prop) : (term131 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51681 {C : Type'} (t : Prop) : (term131 C t) = t.
Proof. exact (@lem51680 C t). Qed.
Lemma lem51682 {C : Type'} : (term130 C) = True.
Proof. exact (@lem51681 C True). Qed.
Lemma lem51683 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) (p1' : B) : (term46 A B C D f p1 p1') = True.
Proof. exact (TRANS (@lem51678 A B C D f p1 p1') (@lem51682 C)). Qed.
Lemma lem51684 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term48 A B C D f p1) = (term129 B).
Proof. exact (fun_ext (fun p1' : B => @lem51683 A B C D f p1 p1')). Qed.
Lemma lem51685 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51686 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term49 A B C D f p1) = (term130 B).
Proof. exact (MK_COMB (@lem51685 B) (@lem51684 A B C D f p1)). Qed.
Lemma lem51688 {A : Type'} (t : Prop) : (term131 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51689 {B : Type'} (t : Prop) : (term131 B t) = t.
Proof. exact (@lem51688 B t). Qed.
Lemma lem51690 {B : Type'} : (term130 B) = True.
Proof. exact (@lem51689 B True). Qed.
Lemma lem51691 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term49 A B C D f p1) = True.
Proof. exact (TRANS (@lem51686 A B C D f p1) (@lem51690 B)). Qed.
Lemma lem51692 {A B C D : Type'} (f : type1198 A B C D) (p1 : A) : (term28 A B C D f p1) = True.
Proof. exact (TRANS (@lem51480 A B C D f p1) (@lem51691 A B C D f p1)). Qed.
Lemma lem51693 {A B C D : Type'} (f : type1198 A B C D) : (term30 A B C D f) = (term129 A).
Proof. exact (fun_ext (fun p1 : A => @lem51692 A B C D f p1)). Qed.
Lemma lem51694 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51695 {A B C D : Type'} (f : type1198 A B C D) : (term31 A B C D f) = (term130 A).
Proof. exact (MK_COMB (@lem51694 A) (@lem51693 A B C D f)). Qed.
Lemma lem51697 {A : Type'} (t : Prop) : (term131 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51698 {A : Type'} (t : Prop) : (term131 A t) = t.
Proof. exact (@lem51697 A t). Qed.
Lemma lem51699 {A : Type'} : (term130 A) = True.
Proof. exact (@lem51698 A True). Qed.
Lemma lem51700 {A B C D : Type'} (f : type1198 A B C D) : (term31 A B C D f) = True.
Proof. exact (TRANS (@lem51695 A B C D f) (@lem51699 A)). Qed.
Lemma lem51701 {A B C D : Type'} (f : type1198 A B C D) : ((term8 A B C D f) = (term9 A B C D f)) = True.
Proof. exact (TRANS (@lem51457 A B C D f) (@lem51700 A B C D f)). Qed.
Lemma lem51702 {A B C D : Type'} : (term132 A B C D) = (term133 A B C D).
Proof. exact (fun_ext (fun f : type1198 A B C D => @lem51701 A B C D f)). Qed.
Lemma lem51703 {A B C D : Type'} : (@all ((prod A (prod B C)) -> D)) = (@all ((prod A (prod B C)) -> D)).
Proof. exact (eq_refl (@all ((prod A (prod B C)) -> D))). Qed.
Lemma lem51704 {A B C D : Type'} : (term134 A B C D) = (term135 A B C D).
Proof. exact (MK_COMB (@lem51703 A B C D) (@lem51702 A B C D)). Qed.
Lemma lem51706 {A : Type'} (t : Prop) : (term131 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51707 {A B C D : Type'} (t : Prop) : (term136 A B C D t) = t.
Proof. exact (@lem51706 (type1198 A B C D) t). Qed.
Lemma lem51708 {A B C D : Type'} : (term135 A B C D) = True.
Proof. exact (@lem51707 A B C D True). Qed.
Lemma lem51709 {A B C D : Type'} : (term134 A B C D) = True.
Proof. exact (TRANS (@lem51704 A B C D) (@lem51708 A B C D)). Qed.
Lemma lem51710 {A B C D : Type'} : True = (term134 A B C D).
Proof. exact (SYM (@lem51709 A B C D)). Qed.
Lemma lem51711 {A B C D : Type'} : term134 A B C D.
Proof. exact (EQ_MP (@lem51710 A B C D) (@lem0)). Qed.
