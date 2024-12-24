Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_COMPLEMENT_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import COMPL_COMPL_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import IMAGE_ID_spec.
Require Import INTERSECTION_OF_spec.
Require Import INTERS_UNIONS_spec.
Require Import UNIONS_INTERS_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4858520 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4858521 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4858522 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4858521 t1) (@lem4858520 t1)). Qed.
Lemma lem4858523 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4858522 t1 t2). Qed.
Lemma lem4858524 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4858525 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4858524 t1 t2) (@lem4858523 t1 t2)). Qed.
Lemma lem4858526 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4858525 t1 t2 t3). Qed.
Lemma lem4858527 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4858528 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4858527 t1 t2 t3) (@lem4858526 t1 t2 t3)). Qed.
Lemma lem4858529 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4858528 t1 t2 t3)). Qed.
Lemma lem4858533 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4858534 {_111541 : Type'} (s : _111541 -> Prop) (t : _111541 -> Prop) : (s = t) = (term7 _111541 s t).
Proof. exact (@lem4858533 _111541 s t). Qed.
Lemma lem4858535 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term8 _111541 _111543 _111544 g s f) = (term9 _111541 _111543 _111544 f g s)) = (term10 _111541 _111543 _111544 f g s).
Proof. exact (@lem4858534 _111541 (term8 _111541 _111543 _111544 g s f) (term9 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858548 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term10 _111541 _111543 _111544 f g s) = ((term8 _111541 _111543 _111544 g s f) = (term9 _111541 _111543 _111544 f g s)).
Proof. exact (SYM (@lem4858535 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858558 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem4858559 {_111541 : Type'} (P : type919 _111541) (x : _111541) : (term11 _111541 x P) = (term12 _111541 P x).
Proof. exact (@lem4858558 _111541 P x). Qed.
Lemma lem4858560 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) (x : _111541) : (term13 _111541 _111543 _111544 x g s f) = (term14 _111541 _111543 _111544 g s f x).
Proof. exact (@lem4858559 _111541 (term15 _111541 _111543 _111544 g s f) x). Qed.
Lemma lem4858561 {_111541 _111543 _111544 : Type'} (GEN_PVAR_211 : _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term16 _111541 _111543 _111544 g s f GEN_PVAR_211) = (term17 _111541 _111543 _111544 GEN_PVAR_211 g s f).
Proof. exact (eq_refl (term16 _111541 _111543 _111544 g s f GEN_PVAR_211)). Qed.
Lemma lem4858562 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term18 _111541 _111543 _111544 g s f) = (term19 _111541 _111543 _111544 g s f).
Proof. exact (fun_ext (fun GEN_PVAR_211 : _111541 => @lem4858561 _111541 _111543 _111544 GEN_PVAR_211 g s f)). Qed.
Lemma lem4858563 {_111541 : Type'} : (@GSPEC _111541) = (@GSPEC _111541).
Proof. exact (eq_refl (@GSPEC _111541)). Qed.
Lemma lem4858564 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term20 _111541 _111543 _111544 g s f) = (term8 _111541 _111543 _111544 g s f).
Proof. exact (MK_COMB (@lem4858563 _111541) (@lem4858562 _111541 _111543 _111544 g s f)). Qed.
Lemma lem4858565 {_111541 : Type'} (x : _111541) : (@IN _111541 x) = (@IN _111541 x).
Proof. exact (eq_refl (@IN _111541 x)). Qed.
Lemma lem4858566 {_111541 _111543 _111544 : Type'} (x : _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term13 _111541 _111543 _111544 x g s f) = (term21 _111541 _111543 _111544 x g s f).
Proof. exact (MK_COMB (@lem4858565 _111541 x) (@lem4858564 _111541 _111543 _111544 g s f)). Qed.
Lemma lem4858567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4858568 {_111541 _111543 _111544 : Type'} (x : _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term22 _111541 _111543 _111544 x g s f) = (term23 _111541 _111543 _111544 x g s f).
Proof. exact (MK_COMB (@lem4858567) (@lem4858566 _111541 _111543 _111544 x g s f)). Qed.
Lemma lem4858569 {_111541 _111543 _111544 : Type'} (x : _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term14 _111541 _111543 _111544 g s f x) = (term24 _111541 _111543 _111544 x g s f).
Proof. exact (eq_refl (term14 _111541 _111543 _111544 g s f x)). Qed.
Lemma lem4858570 {_111541 _111543 _111544 : Type'} (x : _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : ((term13 _111541 _111543 _111544 x g s f) = (term14 _111541 _111543 _111544 g s f x)) = ((term21 _111541 _111543 _111544 x g s f) = (term24 _111541 _111543 _111544 x g s f)).
Proof. exact (MK_COMB (@lem4858568 _111541 _111543 _111544 x g s f) (@lem4858569 _111541 _111543 _111544 x g s f)). Qed.
Lemma lem4858571 {_111541 _111543 _111544 : Type'} (x : _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : (term21 _111541 _111543 _111544 x g s f) = (term24 _111541 _111543 _111544 x g s f).
Proof. exact (EQ_MP (@lem4858570 _111541 _111543 _111544 x g s f) (@lem4858560 _111541 _111543 _111544 g s f x)). Qed.
Lemma lem4858577 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4858578 {_111541 : Type'} (f : type1538 _111541) (y : Prop) : (term26 _111541 f y) = (f y).
Proof. exact (@lem4858577 Prop (_111541 -> Prop) f y). Qed.
Lemma lem4858579 {_111541 _111543 _111544 : Type'} (x : _111541) (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term27 _111541 _111543 _111544 x y g s) = (term28 _111541 _111543 _111544 x y g s).
Proof. exact (@lem4858578 _111541 (term29 _111541 x) (term30 _111543 _111544 y g s)). Qed.
Lemma lem4858580 {_111541 : Type'} (p : Prop) (x : _111541) : (term31 _111541 x p) = (term32 _111541 p x).
Proof. exact (eq_refl (term31 _111541 x p)). Qed.
Lemma lem4858581 {_111541 : Type'} (x : _111541) : (term33 _111541 x) = (term29 _111541 x).
Proof. exact (fun_ext (fun p : Prop => @lem4858580 _111541 p x)). Qed.
Lemma lem4858582 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term30 _111543 _111544 y g s) = (term30 _111543 _111544 y g s).
Proof. exact (eq_refl (term30 _111543 _111544 y g s)). Qed.
Lemma lem4858583 {_111541 _111543 _111544 : Type'} (x : _111541) (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term27 _111541 _111543 _111544 x y g s) = (term28 _111541 _111543 _111544 x y g s).
Proof. exact (MK_COMB (@lem4858581 _111541 x) (@lem4858582 _111543 _111544 y g s)). Qed.
Lemma lem4858584 {_111541 : Type'} : (@eq (_111541 -> Prop)) = (@eq (_111541 -> Prop)).
Proof. exact (eq_refl (@eq (_111541 -> Prop))). Qed.
Lemma lem4858585 {_111541 _111543 _111544 : Type'} (x : _111541) (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term34 _111541 _111543 _111544 x y g s) = (term35 _111541 _111543 _111544 x y g s).
Proof. exact (MK_COMB (@lem4858584 _111541) (@lem4858583 _111541 _111543 _111544 x y g s)). Qed.
Lemma lem4858586 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) : (term28 _111541 _111543 _111544 x y g s) = (term36 _111541 _111543 _111544 y g s x).
Proof. exact (eq_refl (term28 _111541 _111543 _111544 x y g s)). Qed.
Lemma lem4858587 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) : ((term27 _111541 _111543 _111544 x y g s) = (term28 _111541 _111543 _111544 x y g s)) = ((term28 _111541 _111543 _111544 x y g s) = (term36 _111541 _111543 _111544 y g s x)).
Proof. exact (MK_COMB (@lem4858585 _111541 _111543 _111544 x y g s) (@lem4858586 _111541 _111543 _111544 y g s x)). Qed.
Lemma lem4858588 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) : (term28 _111541 _111543 _111544 x y g s) = (term36 _111541 _111543 _111544 y g s x).
Proof. exact (EQ_MP (@lem4858587 _111541 _111543 _111544 y g s x) (@lem4858579 _111541 _111543 _111544 x y g s)). Qed.
Lemma lem4858592 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term37 A B y f s) = (term38 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4858593 {_111543 _111544 : Type'} (y : _111543) (f : _111544 -> _111543) (s : _111544 -> Prop) : (term30 _111543 _111544 y f s) = (term39 _111543 _111544 y f s).
Proof. exact (@lem4858592 _111544 _111543 y f s). Qed.
Lemma lem4858594 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term30 _111543 _111544 y g s) = (term39 _111543 _111544 y g s).
Proof. exact (@lem4858593 _111543 _111544 y g s). Qed.
Lemma lem4858604 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4858605 {_111544 : Type'} (P : _111544 -> Prop) (x : _111544) : (@IN _111544 x P) = (P x).
Proof. exact (@lem4858604 _111544 P x). Qed.
Lemma lem4858606 {_111544 : Type'} (s : _111544 -> Prop) (x : _111544) : (@IN _111544 x s) = (s x).
Proof. exact (@lem4858605 _111544 s x). Qed.
Lemma lem4858607 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (x : _111544) : (term40 _111543 _111544 y g x) = (term40 _111543 _111544 y g x).
Proof. exact (eq_refl (term40 _111543 _111544 y g x)). Qed.
Lemma lem4858608 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term41 _111543 _111544 y g x s) = (term42 _111543 _111544 y g s x).
Proof. exact (MK_COMB (@lem4858607 _111543 _111544 y g x) (@lem4858606 _111544 s x)). Qed.
Lemma lem4858611 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term43 _111543 _111544 y g s) = (term44 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4858608 _111543 _111544 y g s x)). Qed.
Lemma lem4858612 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4858613 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term39 _111543 _111544 y g s) = (term45 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4858612 _111544) (@lem4858611 _111543 _111544 y g s)). Qed.
Lemma lem4858618 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term30 _111543 _111544 y g s) = (term45 _111543 _111544 y g s).
Proof. exact (TRANS (@lem4858594 _111543 _111544 y g s) (@lem4858613 _111543 _111544 y g s)). Qed.
Lemma lem4858619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858620 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term46 _111543 _111544 y g s) = (term47 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4858619) (@lem4858618 _111543 _111544 y g s)). Qed.
Lemma lem4858623 {_111541 : Type'} (x : _111541) (t : _111541) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem4858624 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (t : _111541) : (term48 _111541 _111543 _111544 y g s x t) = (term49 _111541 _111543 _111544 y g s x t).
Proof. exact (MK_COMB (@lem4858620 _111543 _111544 y g s) (@lem4858623 _111541 x t)). Qed.
Lemma lem4858627 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) : (term36 _111541 _111543 _111544 y g s x) = (term50 _111541 _111543 _111544 y g s x).
Proof. exact (fun_ext (fun t : _111541 => @lem4858624 _111541 _111543 _111544 y g s x t)). Qed.
Lemma lem4858628 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) : (term28 _111541 _111543 _111544 x y g s) = (term50 _111541 _111543 _111544 y g s x).
Proof. exact (TRANS (@lem4858588 _111541 _111543 _111544 y g s x) (@lem4858627 _111541 _111543 _111544 y g s x)). Qed.
Lemma lem4858629 {_111541 _111543 : Type'} (f : _111543 -> _111541) (y : _111543) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem4858630 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term51 _111541 _111543 _111544 x g s f y) = (term52 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4858628 _111541 _111543 _111544 y g s x) (@lem4858629 _111541 _111543 f y)). Qed.
Lemma lem4858632 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4858633 {_111541 : Type'} (f : _111541 -> Prop) (y : _111541) : (term53 _111541 f y) = (f y).
Proof. exact (@lem4858632 _111541 Prop f y). Qed.
Lemma lem4858634 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term54 _111541 _111543 _111544 g s x f y) = (term52 _111541 _111543 _111544 g s x f y).
Proof. exact (@lem4858633 _111541 (term50 _111541 _111543 _111544 y g s x) (f y)). Qed.
Lemma lem4858635 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (t : _111541) : (term55 _111541 _111543 _111544 y g s x t) = (term49 _111541 _111543 _111544 y g s x t).
Proof. exact (eq_refl (term55 _111541 _111543 _111544 y g s x t)). Qed.
Lemma lem4858636 {_111541 _111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) : (term56 _111541 _111543 _111544 y g s x) = (term50 _111541 _111543 _111544 y g s x).
Proof. exact (fun_ext (fun t : _111541 => @lem4858635 _111541 _111543 _111544 y g s x t)). Qed.
Lemma lem4858637 {_111541 _111543 : Type'} (f : _111543 -> _111541) (y : _111543) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem4858638 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term54 _111541 _111543 _111544 g s x f y) = (term52 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4858636 _111541 _111543 _111544 y g s x) (@lem4858637 _111541 _111543 f y)). Qed.
Lemma lem4858639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4858640 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term57 _111541 _111543 _111544 g s x f y) = (term58 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4858639) (@lem4858638 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858641 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term52 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (eq_refl (term52 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858642 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : ((term54 _111541 _111543 _111544 g s x f y) = (term52 _111541 _111543 _111544 g s x f y)) = ((term52 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y)).
Proof. exact (MK_COMB (@lem4858640 _111541 _111543 _111544 g s x f y) (@lem4858641 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858643 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term52 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (EQ_MP (@lem4858642 _111541 _111543 _111544 g s x f y) (@lem4858634 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858656 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term51 _111541 _111543 _111544 x g s f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (TRANS (@lem4858630 _111541 _111543 _111544 g s x f y) (@lem4858643 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858657 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term60 _111541 _111543 _111544 x g s f) = (term61 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4858656 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858658 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4858659 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term24 _111541 _111543 _111544 x g s f) = (term62 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4858658 _111543) (@lem4858657 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4858664 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term21 _111541 _111543 _111544 x g s f) = (term62 _111541 _111543 _111544 g s x f).
Proof. exact (TRANS (@lem4858571 _111541 _111543 _111544 x g s f) (@lem4858659 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4858665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4858666 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term23 _111541 _111543 _111544 x g s f) = (term63 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4858665) (@lem4858664 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4858668 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term37 A B y f s) = (term38 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4858669 {_111541 _111544 : Type'} (y : _111541) (f : _111544 -> _111541) (s : _111544 -> Prop) : (term30 _111541 _111544 y f s) = (term39 _111541 _111544 y f s).
Proof. exact (@lem4858668 _111544 _111541 y f s). Qed.
Lemma lem4858670 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term64 _111541 _111543 _111544 x f g s) = (term65 _111541 _111543 _111544 x f g s).
Proof. exact (@lem4858669 _111541 _111544 x (term66 _111541 _111543 _111544 f g) s). Qed.
Lemma lem4858680 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4858681 {_111541 _111544 : Type'} (f : _111544 -> _111541) (y : _111544) : (term67 _111541 _111544 f y) = (f y).
Proof. exact (@lem4858680 _111544 _111541 f y). Qed.
Lemma lem4858682 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : (term68 _111541 _111543 _111544 f g x) = (term69 _111541 _111543 _111544 f g x).
Proof. exact (@lem4858681 _111541 _111544 (term66 _111541 _111543 _111544 f g) x). Qed.
Lemma lem4858683 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : (term69 _111541 _111543 _111544 f g x) = (term70 _111541 _111543 _111544 f g x).
Proof. exact (eq_refl (term69 _111541 _111543 _111544 f g x)). Qed.
Lemma lem4858684 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) : (term71 _111541 _111543 _111544 f g) = (term66 _111541 _111543 _111544 f g).
Proof. exact (fun_ext (fun x : _111544 => @lem4858683 _111541 _111543 _111544 f g x)). Qed.
Lemma lem4858685 {_111544 : Type'} (x : _111544) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4858686 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : (term68 _111541 _111543 _111544 f g x) = (term69 _111541 _111543 _111544 f g x).
Proof. exact (MK_COMB (@lem4858684 _111541 _111543 _111544 f g) (@lem4858685 _111544 x)). Qed.
Lemma lem4858687 {_111541 : Type'} : (@eq _111541) = (@eq _111541).
Proof. exact (eq_refl (@eq _111541)). Qed.
Lemma lem4858688 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : (term72 _111541 _111543 _111544 f g x) = (term73 _111541 _111543 _111544 f g x).
Proof. exact (MK_COMB (@lem4858687 _111541) (@lem4858686 _111541 _111543 _111544 f g x)). Qed.
Lemma lem4858689 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : (term69 _111541 _111543 _111544 f g x) = (term70 _111541 _111543 _111544 f g x).
Proof. exact (eq_refl (term69 _111541 _111543 _111544 f g x)). Qed.
Lemma lem4858690 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : ((term68 _111541 _111543 _111544 f g x) = (term69 _111541 _111543 _111544 f g x)) = ((term69 _111541 _111543 _111544 f g x) = (term70 _111541 _111543 _111544 f g x)).
Proof. exact (MK_COMB (@lem4858688 _111541 _111543 _111544 f g x) (@lem4858689 _111541 _111543 _111544 f g x)). Qed.
Lemma lem4858691 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x : _111544) : (term69 _111541 _111543 _111544 f g x) = (term70 _111541 _111543 _111544 f g x).
Proof. exact (EQ_MP (@lem4858690 _111541 _111543 _111544 f g x) (@lem4858682 _111541 _111543 _111544 f g x)). Qed.
Lemma lem4858692 {_111541 : Type'} (x : _111541) : (@eq _111541 x) = (@eq _111541 x).
Proof. exact (eq_refl (@eq _111541 x)). Qed.
Lemma lem4858693 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (x = (term69 _111541 _111543 _111544 f g x')) = (x = (term70 _111541 _111543 _111544 f g x')).
Proof. exact (MK_COMB (@lem4858692 _111541 x) (@lem4858691 _111541 _111543 _111544 f g x')). Qed.
Lemma lem4858696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858697 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term74 _111541 _111543 _111544 x f g x') = (term75 _111541 _111543 _111544 x f g x').
Proof. exact (MK_COMB (@lem4858696) (@lem4858693 _111541 _111543 _111544 x f g x')). Qed.
Lemma lem4858699 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4858700 {_111544 : Type'} (P : _111544 -> Prop) (x : _111544) : (@IN _111544 x P) = (P x).
Proof. exact (@lem4858699 _111544 P x). Qed.
Lemma lem4858701 {_111544 : Type'} (s : _111544 -> Prop) (x : _111544) : (@IN _111544 x s) = (s x).
Proof. exact (@lem4858700 _111544 s x). Qed.
Lemma lem4858702 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term76 _111541 _111543 _111544 x f g x' s) = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (MK_COMB (@lem4858697 _111541 _111543 _111544 x f g x') (@lem4858701 _111544 s x')). Qed.
Lemma lem4858705 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term78 _111541 _111543 _111544 x f g s) = (term79 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4858702 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4858706 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4858707 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term65 _111541 _111543 _111544 x f g s) = (term80 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4858706 _111544) (@lem4858705 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858712 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term64 _111541 _111543 _111544 x f g s) = (term80 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4858670 _111541 _111543 _111544 x f g s) (@lem4858707 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858713 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term21 _111541 _111543 _111544 x g s f) = (term64 _111541 _111543 _111544 x f g s)) = ((term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s)).
Proof. exact (MK_COMB (@lem4858666 _111541 _111543 _111544 g s x f) (@lem4858712 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858716 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term81 _111541 _111543 _111544 f g s) = (term82 _111541 _111543 _111544 f g s).
Proof. exact (fun_ext (fun x : _111541 => @lem4858713 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858717 {_111541 : Type'} : (@all _111541) = (@all _111541).
Proof. exact (eq_refl (@all _111541)). Qed.
Lemma lem4858718 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term10 _111541 _111543 _111544 f g s) = (term83 _111541 _111543 _111544 f g s).
Proof. exact (MK_COMB (@lem4858717 _111541) (@lem4858716 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858723 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term83 _111541 _111543 _111544 f g s) = (term10 _111541 _111543 _111544 f g s).
Proof. exact (SYM (@lem4858718 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858725 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4858726 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term83 _111541 _111543 _111544 f g s) = (term85 _111541 _111543 _111544 f g s).
Proof. exact (@lem4858725 (term83 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858727 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term85 _111541 _111543 _111544 f g s) = (term83 _111541 _111543 _111544 f g s).
Proof. exact (SYM (@lem4858726 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858728 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term86 _111541 _111543 _111544 f g s) : term86 _111541 _111543 _111544 f g s.
Proof. exact (h1). Qed.
Lemma lem4858731 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term85 _111541 _111543 _111544 f g s) : term85 _111541 _111543 _111544 f g s.
Proof. exact (h1). Qed.
Lemma lem4858732 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term87 _111541 _111543 _111544 f g s.
Proof. exact (fun h0 : term85 _111541 _111543 _111544 f g s => @lem4858731 _111541 _111543 _111544 f g s h0). Qed.
Lemma lem4858733 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term87 _111541 _111543 _111544 f g s) : term87 _111541 _111543 _111544 f g s.
Proof. exact (h1). Qed.
Lemma lem4858734 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term85 _111541 _111543 _111544 f g s) : term85 _111541 _111543 _111544 f g s.
Proof. exact (h1). Qed.
Lemma lem4858735 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term85 _111541 _111543 _111544 f g s) (h2 : term87 _111541 _111543 _111544 f g s) : term85 _111541 _111543 _111544 f g s.
Proof. exact (@lem4858733 _111541 _111543 _111544 f g s h2 (@lem4858734 _111541 _111543 _111544 f g s h1)). Qed.
Lemma lem4858736 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term85 _111541 _111543 _111544 f g s) : term88 _111541 _111543 _111544 f g s.
Proof. exact (fun h0 : term87 _111541 _111543 _111544 f g s => @lem4858735 _111541 _111543 _111544 f g s h1 h0). Qed.
Lemma lem4858737 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term87 _111541 _111543 _111544 f g s) : term87 _111541 _111543 _111544 f g s.
Proof. exact (h1). Qed.
Lemma lem4858738 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term85 _111541 _111543 _111544 f g s) (h2 : term87 _111541 _111543 _111544 f g s) : term85 _111541 _111543 _111544 f g s.
Proof. exact (@lem4858736 _111541 _111543 _111544 f g s h1 (@lem4858737 _111541 _111543 _111544 f g s h2)). Qed.
Lemma lem4858739 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term87 _111541 _111543 _111544 f g s) : term87 _111541 _111543 _111544 f g s.
Proof. exact (fun h0 : term85 _111541 _111543 _111544 f g s => @lem4858738 _111541 _111543 _111544 f g s h0 h1). Qed.
Lemma lem4858740 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term89 _111541 _111543 _111544 f g s.
Proof. exact (fun h0 : term87 _111541 _111543 _111544 f g s => @lem4858739 _111541 _111543 _111544 f g s h0). Qed.
Lemma lem4858743 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term87 _111541 _111543 _111544 f g s.
Proof. exact (@lem4858740 _111541 _111543 _111544 f g s (@lem4858732 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858744 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term87 _111541 _111543 _111544 f g s.
Proof. exact (@lem4858743 _111541 _111543 _111544 f g s). Qed.
Lemma lem4858758 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4858759 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term85 _111541 _111543 _111544 f g s) = (term90 _111541 _111543 _111544 f g s).
Proof. exact (@lem4858758 (term86 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858761 (t : Prop) : (term91 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4858762 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term90 _111541 _111543 _111544 f g s) = (term83 _111541 _111543 _111544 f g s).
Proof. exact (@lem4858761 (term83 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858767 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term85 _111541 _111543 _111544 f g s) = (term83 _111541 _111543 _111544 f g s).
Proof. exact (TRANS (@lem4858759 _111541 _111543 _111544 f g s) (@lem4858762 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858886 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : (term92 _111541 _111543 _111544 g s) = (term93 _111541 _111543 _111544 g s).
Proof. exact (fun_ext (fun f : _111543 -> _111541 => @lem4858767 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858887 {_111541 _111543 : Type'} : (@all (_111543 -> _111541)) = (@all (_111543 -> _111541)).
Proof. exact (eq_refl (@all (_111543 -> _111541))). Qed.
Lemma lem4858888 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : (term94 _111541 _111543 _111544 g s) = (term95 _111541 _111543 _111544 g s).
Proof. exact (MK_COMB (@lem4858887 _111541 _111543) (@lem4858886 _111541 _111543 _111544 g s)). Qed.
Lemma lem4858893 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : (term96 _111541 _111543 _111544 s) = (term97 _111541 _111543 _111544 s).
Proof. exact (fun_ext (fun g : _111544 -> _111543 => @lem4858888 _111541 _111543 _111544 g s)). Qed.
Lemma lem4858894 {_111543 _111544 : Type'} : (@all (_111544 -> _111543)) = (@all (_111544 -> _111543)).
Proof. exact (eq_refl (@all (_111544 -> _111543))). Qed.
Lemma lem4858895 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : (term98 _111541 _111543 _111544 s) = (term99 _111541 _111543 _111544 s).
Proof. exact (MK_COMB (@lem4858894 _111543 _111544) (@lem4858893 _111541 _111543 _111544 s)). Qed.
Lemma lem4858900 {_111541 _111543 _111544 : Type'} : (term100 _111541 _111543 _111544) = (term101 _111541 _111543 _111544).
Proof. exact (fun_ext (fun s : _111544 -> Prop => @lem4858895 _111541 _111543 _111544 s)). Qed.
Lemma lem4858901 {_111544 : Type'} : (@all (_111544 -> Prop)) = (@all (_111544 -> Prop)).
Proof. exact (eq_refl (@all (_111544 -> Prop))). Qed.
Lemma lem4858910 {_111541 _111543 _111544 : Type'} : (term102 _111541 _111543 _111544) = (term103 _111541 _111543 _111544).
Proof. exact (MK_COMB (@lem4858901 _111544) (@lem4858900 _111541 _111543 _111544)). Qed.
Lemma lem4858915 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term77 _111541 _111543 _111544 x f g s x') = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term77 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4858916 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term79 _111541 _111543 _111544 x f g s) = (term79 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4858915 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4858917 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4858918 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term80 _111541 _111543 _111544 x f g s) = (term80 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4858917 _111544) (@lem4858916 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858919 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4858924 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term42 _111543 _111544 y g s x) = (term42 _111543 _111544 y g s x).
Proof. exact (eq_refl (term42 _111543 _111544 y g s x)). Qed.
Lemma lem4858925 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term44 _111543 _111544 y g s) = (term44 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4858924 _111543 _111544 y g s x)). Qed.
Lemma lem4858926 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4858927 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term45 _111543 _111544 y g s) = (term45 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4858926 _111544) (@lem4858925 _111543 _111544 y g s)). Qed.
Lemma lem4858928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858929 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term47 _111543 _111544 y g s) = (term47 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4858928) (@lem4858927 _111543 _111544 y g s)). Qed.
Lemma lem4858930 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term59 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4858929 _111543 _111544 y g s) (@lem4858919 _111541 _111543 x f y)). Qed.
Lemma lem4858931 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term61 _111541 _111543 _111544 g s x f) = (term61 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4858930 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4858932 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4858933 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term62 _111541 _111543 _111544 g s x f) = (term62 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4858932 _111543) (@lem4858931 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4858934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4858935 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term63 _111541 _111543 _111544 g s x f) = (term63 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4858934) (@lem4858933 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4858936 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s)) = ((term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s)).
Proof. exact (MK_COMB (@lem4858935 _111541 _111543 _111544 g s x f) (@lem4858918 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858937 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term82 _111541 _111543 _111544 f g s) = (term82 _111541 _111543 _111544 f g s).
Proof. exact (fun_ext (fun x : _111541 => @lem4858936 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4858938 {_111541 : Type'} : (@all _111541) = (@all _111541).
Proof. exact (eq_refl (@all _111541)). Qed.
Lemma lem4858939 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term83 _111541 _111543 _111544 f g s) = (term83 _111541 _111543 _111544 f g s).
Proof. exact (MK_COMB (@lem4858938 _111541) (@lem4858937 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858940 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : (term93 _111541 _111543 _111544 g s) = (term93 _111541 _111543 _111544 g s).
Proof. exact (fun_ext (fun f : _111543 -> _111541 => @lem4858939 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4858941 {_111541 _111543 : Type'} : (@all (_111543 -> _111541)) = (@all (_111543 -> _111541)).
Proof. exact (eq_refl (@all (_111543 -> _111541))). Qed.
Lemma lem4858942 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : (term95 _111541 _111543 _111544 g s) = (term95 _111541 _111543 _111544 g s).
Proof. exact (MK_COMB (@lem4858941 _111541 _111543) (@lem4858940 _111541 _111543 _111544 g s)). Qed.
Lemma lem4858943 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : (term97 _111541 _111543 _111544 s) = (term97 _111541 _111543 _111544 s).
Proof. exact (fun_ext (fun g : _111544 -> _111543 => @lem4858942 _111541 _111543 _111544 g s)). Qed.
Lemma lem4858944 {_111543 _111544 : Type'} : (@all (_111544 -> _111543)) = (@all (_111544 -> _111543)).
Proof. exact (eq_refl (@all (_111544 -> _111543))). Qed.
Lemma lem4858945 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : (term99 _111541 _111543 _111544 s) = (term99 _111541 _111543 _111544 s).
Proof. exact (MK_COMB (@lem4858944 _111543 _111544) (@lem4858943 _111541 _111543 _111544 s)). Qed.
Lemma lem4858946 {_111541 _111543 _111544 : Type'} : (term101 _111541 _111543 _111544) = (term101 _111541 _111543 _111544).
Proof. exact (fun_ext (fun s : _111544 -> Prop => @lem4858945 _111541 _111543 _111544 s)). Qed.
Lemma lem4858947 {_111544 : Type'} : (@all (_111544 -> Prop)) = (@all (_111544 -> Prop)).
Proof. exact (eq_refl (@all (_111544 -> Prop))). Qed.
Lemma lem4858948 {_111541 _111543 _111544 : Type'} : (term103 _111541 _111543 _111544) = (term103 _111541 _111543 _111544).
Proof. exact (MK_COMB (@lem4858947 _111544) (@lem4858946 _111541 _111543 _111544)). Qed.
Lemma lem4858999 {_111541 _111543 _111544 : Type'} : (term102 _111541 _111543 _111544) = (term103 _111541 _111543 _111544).
Proof. exact (TRANS (@lem4858910 _111541 _111543 _111544) (@lem4858948 _111541 _111543 _111544)). Qed.
Lemma lem4859000 {_111541 _111543 _111544 : Type'} : (term103 _111541 _111543 _111544) = (term102 _111541 _111543 _111544).
Proof. exact (SYM (@lem4858999 _111541 _111543 _111544)). Qed.
Lemma lem4859002 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4859003 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s)) = (term104 _111541 _111543 _111544 x f g s).
Proof. exact (@lem4859002 ((term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s))). Qed.
Lemma lem4859004 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term104 _111541 _111543 _111544 x f g s) = ((term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s)).
Proof. exact (SYM (@lem4859003 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859005 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term105 _111541 _111543 _111544 x f g s) : term105 _111541 _111543 _111544 x f g s.
Proof. exact (h1). Qed.
Lemma lem4859014 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term106 _111543 _111544 y g s x) = (term107 _111543 _111544 y g s x).
Proof. exact (@lem17045 (y = (g x)) (s x)). Qed.
Lemma lem4859017 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term42 _111543 _111544 y g s x) = (term42 _111543 _111544 y g s x).
Proof. exact (eq_refl (term42 _111543 _111544 y g s x)). Qed.
Lemma lem4859018 {_111544 : Type'} (P : _111544 -> Prop) : (term108 _111544 P) = (term109 _111544 P).
Proof. exact (@lem18394 _111544 P). Qed.
Lemma lem4859019 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term110 _111543 _111544 y g s) = (term111 _111543 _111544 y g s).
Proof. exact (@lem4859018 _111544 (term44 _111543 _111544 y g s)). Qed.
Lemma lem4859020 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term112 _111543 _111544 y g s x) = (term42 _111543 _111544 y g s x).
Proof. exact (eq_refl (term112 _111543 _111544 y g s x)). Qed.
Lemma lem4859021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4859022 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term113 _111543 _111544 y g s x) = (term106 _111543 _111544 y g s x).
Proof. exact (MK_COMB (@lem4859021) (@lem4859020 _111543 _111544 y g s x)). Qed.
Lemma lem4859023 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term113 _111543 _111544 y g s x) = (term107 _111543 _111544 y g s x).
Proof. exact (TRANS (@lem4859022 _111543 _111544 y g s x) (@lem4859014 _111543 _111544 y g s x)). Qed.
Lemma lem4859024 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term114 _111543 _111544 y g s) = (term115 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4859023 _111543 _111544 y g s x)). Qed.
Lemma lem4859025 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859026 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term111 _111543 _111544 y g s) = (term116 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859025 _111544) (@lem4859024 _111543 _111544 y g s)). Qed.
Lemma lem4859027 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term110 _111543 _111544 y g s) = (term116 _111543 _111544 y g s).
Proof. exact (TRANS (@lem4859019 _111543 _111544 y g s) (@lem4859026 _111543 _111544 y g s)). Qed.
Lemma lem4859028 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term44 _111543 _111544 y g s) = (term44 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4859017 _111543 _111544 y g s x)). Qed.
Lemma lem4859029 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859030 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term45 _111543 _111544 y g s) = (term45 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859029 _111544) (@lem4859028 _111543 _111544 y g s)). Qed.
Lemma lem4859031 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term117 _111541 _111543 x f y) = (term117 _111541 _111543 x f y).
Proof. exact (eq_refl (term117 _111541 _111543 x f y)). Qed.
Lemma lem4859032 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4859033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859034 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term118 _111543 _111544 y g s) = (term119 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859033) (@lem4859027 _111543 _111544 y g s)). Qed.
Lemma lem4859035 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term120 _111541 _111543 _111544 g s x f y) = (term121 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859034 _111543 _111544 y g s) (@lem4859031 _111541 _111543 x f y)). Qed.
Lemma lem4859036 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term122 _111541 _111543 _111544 g s x f y) = (term120 _111541 _111543 _111544 g s x f y).
Proof. exact (@lem17045 (term45 _111543 _111544 y g s) (x = (f y))). Qed.
Lemma lem4859037 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term122 _111541 _111543 _111544 g s x f y) = (term121 _111541 _111543 _111544 g s x f y).
Proof. exact (TRANS (@lem4859036 _111541 _111543 _111544 g s x f y) (@lem4859035 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859039 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term47 _111543 _111544 y g s) = (term47 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859038) (@lem4859030 _111543 _111544 y g s)). Qed.
Lemma lem4859040 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term59 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859039 _111543 _111544 y g s) (@lem4859032 _111541 _111543 x f y)). Qed.
Lemma lem4859041 {_111543 : Type'} (P : _111543 -> Prop) : (term108 _111543 P) = (term109 _111543 P).
Proof. exact (@lem18394 _111543 P). Qed.
Lemma lem4859042 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term123 _111541 _111543 _111544 g s x f) = (term124 _111541 _111543 _111544 g s x f).
Proof. exact (@lem4859041 _111543 (term61 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859043 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term125 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (eq_refl (term125 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4859045 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term126 _111541 _111543 _111544 g s x f y) = (term122 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859044) (@lem4859043 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859046 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term126 _111541 _111543 _111544 g s x f y) = (term121 _111541 _111543 _111544 g s x f y).
Proof. exact (TRANS (@lem4859045 _111541 _111543 _111544 g s x f y) (@lem4859037 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859047 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term127 _111541 _111543 _111544 g s x f) = (term128 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859046 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859048 {_111543 : Type'} : (@all _111543) = (@all _111543).
Proof. exact (eq_refl (@all _111543)). Qed.
Lemma lem4859049 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term124 _111541 _111543 _111544 g s x f) = (term129 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859048 _111543) (@lem4859047 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859050 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term123 _111541 _111543 _111544 g s x f) = (term129 _111541 _111543 _111544 g s x f).
Proof. exact (TRANS (@lem4859042 _111541 _111543 _111544 g s x f) (@lem4859049 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859051 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term61 _111541 _111543 _111544 g s x f) = (term61 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859040 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859052 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859053 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term62 _111541 _111543 _111544 g s x f) = (term62 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859052 _111543) (@lem4859051 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859062 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term130 _111541 _111543 _111544 x f g s x') = (term131 _111541 _111543 _111544 x f g s x').
Proof. exact (@lem17045 (x = (term70 _111541 _111543 _111544 f g x')) (s x')). Qed.
Lemma lem4859065 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term77 _111541 _111543 _111544 x f g s x') = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term77 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859066 {_111544 : Type'} (P : _111544 -> Prop) : (term108 _111544 P) = (term109 _111544 P).
Proof. exact (@lem18394 _111544 P). Qed.
Lemma lem4859067 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term132 _111541 _111543 _111544 x f g s) = (term133 _111541 _111543 _111544 x f g s).
Proof. exact (@lem4859066 _111544 (term79 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859068 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term134 _111541 _111543 _111544 x f g s x') = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term134 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4859070 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term135 _111541 _111543 _111544 x f g s x') = (term130 _111541 _111543 _111544 x f g s x').
Proof. exact (MK_COMB (@lem4859069) (@lem4859068 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859071 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term135 _111541 _111543 _111544 x f g s x') = (term131 _111541 _111543 _111544 x f g s x').
Proof. exact (TRANS (@lem4859070 _111541 _111543 _111544 x f g s x') (@lem4859062 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859072 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term136 _111541 _111543 _111544 x f g s) = (term137 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859071 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859073 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859074 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term133 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859073 _111544) (@lem4859072 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859075 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term132 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859067 _111541 _111543 _111544 x f g s) (@lem4859074 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859076 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term79 _111541 _111543 _111544 x f g s) = (term79 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859065 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859077 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859078 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term80 _111541 _111543 _111544 x f g s) = (term80 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859077 _111544) (@lem4859076 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859080 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term139 _111541 _111543 _111544 g s x f) = (term140 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859079) (@lem4859050 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859081 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term141 _111541 _111543 _111544 x f g s) = (term142 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859080 _111541 _111543 _111544 g s x f) (@lem4859078 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859083 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term143 _111541 _111543 _111544 g s x f) = (term143 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859082) (@lem4859053 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859084 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term144 _111541 _111543 _111544 x f g s) = (term145 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859083 _111541 _111543 _111544 g s x f) (@lem4859075 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859086 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term146 _111541 _111543 _111544 x f g s) = (term147 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859085) (@lem4859084 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859087 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term148 _111541 _111543 _111544 x f g s) = (term149 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859086 _111541 _111543 _111544 x f g s) (@lem4859081 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859088 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term105 _111541 _111543 _111544 x f g s) = (term148 _111541 _111543 _111544 x f g s).
Proof. exact (@lem17646 (term62 _111541 _111543 _111544 g s x f) (term80 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859089 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term105 _111541 _111543 _111544 x f g s) = (term149 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859088 _111541 _111543 _111544 x f g s) (@lem4859087 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859348 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4859349 {_111544 : Type'} (P : _111544 -> Prop) (Q : Prop) : (term150 _111544 P Q) = (term151 _111544 P Q).
Proof. exact (@lem4859348 _111544 P Q). Qed.
Lemma lem4859350 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term152 _111541 _111543 _111544 g s x f y) = (term153 _111541 _111543 _111544 g s x f y).
Proof. exact (@lem4859349 _111544 (term44 _111543 _111544 y g s) (x = (f y))). Qed.
Lemma lem4859351 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term112 _111543 _111544 y g s x) = (term42 _111543 _111544 y g s x).
Proof. exact (eq_refl (term112 _111543 _111544 y g s x)). Qed.
Lemma lem4859352 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term154 _111543 _111544 y g s) = (term44 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4859351 _111543 _111544 y g s x)). Qed.
Lemma lem4859353 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859354 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term155 _111543 _111544 y g s) = (term45 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859353 _111544) (@lem4859352 _111543 _111544 y g s)). Qed.
Lemma lem4859355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859356 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term156 _111543 _111544 y g s) = (term47 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859355) (@lem4859354 _111543 _111544 y g s)). Qed.
Lemma lem4859357 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4859358 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term152 _111541 _111543 _111544 g s x f y) = (term59 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859356 _111543 _111544 y g s) (@lem4859357 _111541 _111543 x f y)). Qed.
Lemma lem4859359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859360 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term157 _111541 _111543 _111544 g s x f y) = (term158 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859359) (@lem4859358 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859361 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term112 _111543 _111544 y g s x) = (term42 _111543 _111544 y g s x).
Proof. exact (eq_refl (term112 _111543 _111544 y g s x)). Qed.
Lemma lem4859362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859363 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term159 _111543 _111544 y g s x) = (term160 _111543 _111544 y g s x).
Proof. exact (MK_COMB (@lem4859362) (@lem4859361 _111543 _111544 y g s x)). Qed.
Lemma lem4859364 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4859365 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) (x' : _111541) (f : _111543 -> _111541) (y : _111543) : (term161 _111541 _111543 _111544 g s x x' f y) = (term162 _111541 _111543 _111544 g s x x' f y).
Proof. exact (MK_COMB (@lem4859363 _111543 _111544 y g s x) (@lem4859364 _111541 _111543 x' f y)). Qed.
Lemma lem4859366 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term163 _111541 _111543 _111544 g s x f y) = (term164 _111541 _111543 _111544 g s x f y).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859365 _111541 _111543 _111544 g s x' x f y)). Qed.
Lemma lem4859367 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859368 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term153 _111541 _111543 _111544 g s x f y) = (term165 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859367 _111544) (@lem4859366 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859369 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : ((term152 _111541 _111543 _111544 g s x f y) = (term153 _111541 _111543 _111544 g s x f y)) = ((term59 _111541 _111543 _111544 g s x f y) = (term165 _111541 _111543 _111544 g s x f y)).
Proof. exact (MK_COMB (@lem4859360 _111541 _111543 _111544 g s x f y) (@lem4859368 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859370 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term59 _111541 _111543 _111544 g s x f y) = (term165 _111541 _111543 _111544 g s x f y).
Proof. exact (EQ_MP (@lem4859369 _111541 _111543 _111544 g s x f y) (@lem4859350 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859371 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term61 _111541 _111543 _111544 g s x f) = (term166 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859370 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859372 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859373 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term62 _111541 _111543 _111544 g s x f) = (term167 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859372 _111543) (@lem4859371 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859375 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term143 _111541 _111543 _111544 g s x f) = (term168 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859374) (@lem4859373 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859376 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859377 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term145 _111541 _111543 _111544 x f g s) = (term169 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859375 _111541 _111543 _111544 g s x f) (@lem4859376 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859379 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4859380 {_111543 : Type'} (P : _111543 -> Prop) (Q : Prop) : (term150 _111543 P Q) = (term151 _111543 P Q).
Proof. exact (@lem4859379 _111543 P Q). Qed.
Lemma lem4859381 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term170 _111541 _111543 _111544 x f g s) = (term171 _111541 _111543 _111544 x f g s).
Proof. exact (@lem4859380 _111543 (term166 _111541 _111543 _111544 g s x f) (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859382 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term172 _111541 _111543 _111544 g s x f y) = (term165 _111541 _111543 _111544 g s x f y).
Proof. exact (eq_refl (term172 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859383 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term173 _111541 _111543 _111544 g s x f) = (term166 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859382 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859384 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859385 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term174 _111541 _111543 _111544 g s x f) = (term167 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859384 _111543) (@lem4859383 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859387 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term175 _111541 _111543 _111544 g s x f) = (term168 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859386) (@lem4859385 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859388 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859389 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term170 _111541 _111543 _111544 x f g s) = (term169 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859387 _111541 _111543 _111544 g s x f) (@lem4859388 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859391 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term176 _111541 _111543 _111544 x f g s) = (term177 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859390) (@lem4859389 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859392 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term172 _111541 _111543 _111544 g s x f y) = (term165 _111541 _111543 _111544 g s x f y).
Proof. exact (eq_refl (term172 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859394 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term178 _111541 _111543 _111544 g s x f y) = (term179 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859393) (@lem4859392 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859395 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859396 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term180 _111541 _111543 _111544 y x f g s) = (term181 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859394 _111541 _111543 _111544 g s x f y) (@lem4859395 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859397 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term182 _111541 _111543 _111544 x f g s) = (term183 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun y : _111543 => @lem4859396 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859398 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859399 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term171 _111541 _111543 _111544 x f g s) = (term184 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859398 _111543) (@lem4859397 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859400 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term170 _111541 _111543 _111544 x f g s) = (term171 _111541 _111543 _111544 x f g s)) = ((term169 _111541 _111543 _111544 x f g s) = (term184 _111541 _111543 _111544 x f g s)).
Proof. exact (MK_COMB (@lem4859391 _111541 _111543 _111544 x f g s) (@lem4859399 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859401 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term169 _111541 _111543 _111544 x f g s) = (term184 _111541 _111543 _111544 x f g s).
Proof. exact (EQ_MP (@lem4859400 _111541 _111543 _111544 x f g s) (@lem4859381 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859403 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4859404 {_111544 : Type'} (P : _111544 -> Prop) (Q : Prop) : (term150 _111544 P Q) = (term151 _111544 P Q).
Proof. exact (@lem4859403 _111544 P Q). Qed.
Lemma lem4859405 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term185 _111541 _111543 _111544 y x f g s) = (term186 _111541 _111543 _111544 y x f g s).
Proof. exact (@lem4859404 _111544 (term164 _111541 _111543 _111544 g s x f y) (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859406 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) (x' : _111541) (f : _111543 -> _111541) (y : _111543) : (term187 _111541 _111543 _111544 g s x' f y x) = (term162 _111541 _111543 _111544 g s x x' f y).
Proof. exact (eq_refl (term187 _111541 _111543 _111544 g s x' f y x)). Qed.
Lemma lem4859407 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term188 _111541 _111543 _111544 g s x f y) = (term164 _111541 _111543 _111544 g s x f y).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859406 _111541 _111543 _111544 g s x' x f y)). Qed.
Lemma lem4859408 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859409 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term189 _111541 _111543 _111544 g s x f y) = (term165 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859408 _111544) (@lem4859407 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859411 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term190 _111541 _111543 _111544 g s x f y) = (term179 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859410) (@lem4859409 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859412 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859413 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term185 _111541 _111543 _111544 y x f g s) = (term181 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859411 _111541 _111543 _111544 g s x f y) (@lem4859412 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859415 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term191 _111541 _111543 _111544 y x f g s) = (term192 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859414) (@lem4859413 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859416 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) (x' : _111541) (f : _111543 -> _111541) (y : _111543) : (term187 _111541 _111543 _111544 g s x' f y x) = (term162 _111541 _111543 _111544 g s x x' f y).
Proof. exact (eq_refl (term187 _111541 _111543 _111544 g s x' f y x)). Qed.
Lemma lem4859417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859418 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) (x' : _111541) (f : _111543 -> _111541) (y : _111543) : (term193 _111541 _111543 _111544 g s x' f y x) = (term194 _111541 _111543 _111544 g s x x' f y).
Proof. exact (MK_COMB (@lem4859417) (@lem4859416 _111541 _111543 _111544 g s x x' f y)). Qed.
Lemma lem4859419 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term138 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859420 {_111541 _111543 _111544 : Type'} (x : _111544) (y : _111543) (x' : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term195 _111541 _111543 _111544 y x x' f g s) = (term196 _111541 _111543 _111544 x y x' f g s).
Proof. exact (MK_COMB (@lem4859418 _111541 _111543 _111544 g s x x' f y) (@lem4859419 _111541 _111543 _111544 x' f g s)). Qed.
Lemma lem4859421 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term197 _111541 _111543 _111544 y x f g s) = (term198 _111541 _111543 _111544 y x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859420 _111541 _111543 _111544 x' y x f g s)). Qed.
Lemma lem4859422 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859423 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term186 _111541 _111543 _111544 y x f g s) = (term199 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859422 _111544) (@lem4859421 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859424 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term185 _111541 _111543 _111544 y x f g s) = (term186 _111541 _111543 _111544 y x f g s)) = ((term181 _111541 _111543 _111544 y x f g s) = (term199 _111541 _111543 _111544 y x f g s)).
Proof. exact (MK_COMB (@lem4859415 _111541 _111543 _111544 y x f g s) (@lem4859423 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859425 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term181 _111541 _111543 _111544 y x f g s) = (term199 _111541 _111543 _111544 y x f g s).
Proof. exact (EQ_MP (@lem4859424 _111541 _111543 _111544 y x f g s) (@lem4859405 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859426 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term183 _111541 _111543 _111544 x f g s) = (term200 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun y : _111543 => @lem4859425 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859427 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859428 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term184 _111541 _111543 _111544 x f g s) = (term201 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859427 _111543) (@lem4859426 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859429 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term169 _111541 _111543 _111544 x f g s) = (term201 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859401 _111541 _111543 _111544 x f g s) (@lem4859428 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859430 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term145 _111541 _111543 _111544 x f g s) = (term201 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859377 _111541 _111543 _111544 x f g s) (@lem4859429 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859431 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859432 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term147 _111541 _111543 _111544 x f g s) = (term202 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859431) (@lem4859430 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859434 {A : Type'} (P : Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4859435 {_111544 : Type'} (P : Prop) (Q : _111544 -> Prop) : (term203 _111544 P Q) = (term204 _111544 P Q).
Proof. exact (@lem4859434 _111544 P Q). Qed.
Lemma lem4859436 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term205 _111541 _111543 _111544 x f g s) = (term206 _111541 _111543 _111544 x f g s).
Proof. exact (@lem4859435 _111544 (term129 _111541 _111543 _111544 g s x f) (term79 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859437 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term134 _111541 _111543 _111544 x f g s x') = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term134 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859438 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term207 _111541 _111543 _111544 x f g s) = (term79 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859437 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859439 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859440 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term208 _111541 _111543 _111544 x f g s) = (term80 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859439 _111544) (@lem4859438 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859441 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term140 _111541 _111543 _111544 g s x f) = (term140 _111541 _111543 _111544 g s x f).
Proof. exact (eq_refl (term140 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859442 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term205 _111541 _111543 _111544 x f g s) = (term142 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859441 _111541 _111543 _111544 g s x f) (@lem4859440 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859444 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term209 _111541 _111543 _111544 x f g s) = (term210 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859443) (@lem4859442 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859445 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term134 _111541 _111543 _111544 x f g s x') = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term134 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859446 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term140 _111541 _111543 _111544 g s x f) = (term140 _111541 _111543 _111544 g s x f).
Proof. exact (eq_refl (term140 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859447 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term211 _111541 _111543 _111544 x f g s x') = (term212 _111541 _111543 _111544 x f g s x').
Proof. exact (MK_COMB (@lem4859446 _111541 _111543 _111544 g s x f) (@lem4859445 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859448 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term213 _111541 _111543 _111544 x f g s) = (term214 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859447 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859449 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859450 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term206 _111541 _111543 _111544 x f g s) = (term215 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859449 _111544) (@lem4859448 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859451 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term205 _111541 _111543 _111544 x f g s) = (term206 _111541 _111543 _111544 x f g s)) = ((term142 _111541 _111543 _111544 x f g s) = (term215 _111541 _111543 _111544 x f g s)).
Proof. exact (MK_COMB (@lem4859444 _111541 _111543 _111544 x f g s) (@lem4859450 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859452 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term142 _111541 _111543 _111544 x f g s) = (term215 _111541 _111543 _111544 x f g s).
Proof. exact (EQ_MP (@lem4859451 _111541 _111543 _111544 x f g s) (@lem4859436 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859453 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term149 _111541 _111543 _111544 x f g s) = (term216 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859432 _111541 _111543 _111544 x f g s) (@lem4859452 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859457 {A : Type'} (P : A -> Prop) (Q : Prop) : (term217 A P Q) = (term218 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4859458 {_111543 : Type'} (P : _111543 -> Prop) (Q : Prop) : (term217 _111543 P Q) = (term218 _111543 P Q).
Proof. exact (@lem4859457 _111543 P Q). Qed.
Lemma lem4859459 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term219 _111541 _111543 _111544 x f g s) = (term220 _111541 _111543 _111544 x f g s).
Proof. exact (@lem4859458 _111543 (term200 _111541 _111543 _111544 x f g s) (term215 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859460 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term221 _111541 _111543 _111544 x f g s y) = (term199 _111541 _111543 _111544 y x f g s).
Proof. exact (eq_refl (term221 _111541 _111543 _111544 x f g s y)). Qed.
Lemma lem4859461 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term222 _111541 _111543 _111544 x f g s) = (term200 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun y : _111543 => @lem4859460 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859462 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859463 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term223 _111541 _111543 _111544 x f g s) = (term201 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859462 _111543) (@lem4859461 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859465 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term224 _111541 _111543 _111544 x f g s) = (term202 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859464) (@lem4859463 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859466 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term215 _111541 _111543 _111544 x f g s) = (term215 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term215 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859467 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term219 _111541 _111543 _111544 x f g s) = (term216 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859465 _111541 _111543 _111544 x f g s) (@lem4859466 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859469 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term225 _111541 _111543 _111544 x f g s) = (term226 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859468) (@lem4859467 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859470 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term221 _111541 _111543 _111544 x f g s y) = (term199 _111541 _111543 _111544 y x f g s).
Proof. exact (eq_refl (term221 _111541 _111543 _111544 x f g s y)). Qed.
Lemma lem4859471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859472 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term227 _111541 _111543 _111544 x f g s y) = (term228 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859471) (@lem4859470 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859473 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term215 _111541 _111543 _111544 x f g s) = (term215 _111541 _111543 _111544 x f g s).
Proof. exact (eq_refl (term215 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859474 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term229 _111541 _111543 _111544 y x f g s) = (term230 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859472 _111541 _111543 _111544 y x f g s) (@lem4859473 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859475 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term231 _111541 _111543 _111544 x f g s) = (term232 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun y : _111543 => @lem4859474 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859476 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859477 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term220 _111541 _111543 _111544 x f g s) = (term233 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859476 _111543) (@lem4859475 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859478 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term219 _111541 _111543 _111544 x f g s) = (term220 _111541 _111543 _111544 x f g s)) = ((term216 _111541 _111543 _111544 x f g s) = (term233 _111541 _111543 _111544 x f g s)).
Proof. exact (MK_COMB (@lem4859469 _111541 _111543 _111544 x f g s) (@lem4859477 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859479 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term216 _111541 _111543 _111544 x f g s) = (term233 _111541 _111543 _111544 x f g s).
Proof. exact (EQ_MP (@lem4859478 _111541 _111543 _111544 x f g s) (@lem4859459 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859481 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4859482 {_111544 : Type'} (P : _111544 -> Prop) (Q : _111544 -> Prop) : (term234 _111544 P Q) = (term235 _111544 P Q).
Proof. exact (@lem4859481 _111544 P Q). Qed.
Lemma lem4859483 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term236 _111541 _111543 _111544 y x f g s) = (term237 _111541 _111543 _111544 y x f g s).
Proof. exact (@lem4859482 _111544 (term198 _111541 _111543 _111544 y x f g s) (term214 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859484 {_111541 _111543 _111544 : Type'} (x : _111544) (y : _111543) (x' : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term238 _111541 _111543 _111544 y x' f g s x) = (term196 _111541 _111543 _111544 x y x' f g s).
Proof. exact (eq_refl (term238 _111541 _111543 _111544 y x' f g s x)). Qed.
Lemma lem4859485 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term239 _111541 _111543 _111544 y x f g s) = (term198 _111541 _111543 _111544 y x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859484 _111541 _111543 _111544 x' y x f g s)). Qed.
Lemma lem4859486 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859487 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term240 _111541 _111543 _111544 y x f g s) = (term199 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859486 _111544) (@lem4859485 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859489 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term241 _111541 _111543 _111544 y x f g s) = (term228 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859488) (@lem4859487 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859490 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term242 _111541 _111543 _111544 x f g s x') = (term212 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term242 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859491 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term243 _111541 _111543 _111544 x f g s) = (term214 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859490 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859492 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859493 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term244 _111541 _111543 _111544 x f g s) = (term215 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859492 _111544) (@lem4859491 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859494 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term236 _111541 _111543 _111544 y x f g s) = (term230 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859489 _111541 _111543 _111544 y x f g s) (@lem4859493 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859496 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term245 _111541 _111543 _111544 y x f g s) = (term246 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859495) (@lem4859494 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859497 {_111541 _111543 _111544 : Type'} (x : _111544) (y : _111543) (x' : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term238 _111541 _111543 _111544 y x' f g s x) = (term196 _111541 _111543 _111544 x y x' f g s).
Proof. exact (eq_refl (term238 _111541 _111543 _111544 y x' f g s x)). Qed.
Lemma lem4859498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859499 {_111541 _111543 _111544 : Type'} (x : _111544) (y : _111543) (x' : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term247 _111541 _111543 _111544 y x' f g s x) = (term248 _111541 _111543 _111544 x y x' f g s).
Proof. exact (MK_COMB (@lem4859498) (@lem4859497 _111541 _111543 _111544 x y x' f g s)). Qed.
Lemma lem4859500 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term242 _111541 _111543 _111544 x f g s x') = (term212 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term242 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859501 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term249 _111541 _111543 _111544 y x f g s x') = (term250 _111541 _111543 _111544 y x f g s x').
Proof. exact (MK_COMB (@lem4859499 _111541 _111543 _111544 x' y x f g s) (@lem4859500 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859502 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term251 _111541 _111543 _111544 y x f g s) = (term252 _111541 _111543 _111544 y x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859501 _111541 _111543 _111544 y x f g s x')). Qed.
Lemma lem4859503 {_111544 : Type'} : (@ex _111544) = (@ex _111544).
Proof. exact (eq_refl (@ex _111544)). Qed.
Lemma lem4859504 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term237 _111541 _111543 _111544 y x f g s) = (term253 _111541 _111543 _111544 y x f g s).
Proof. exact (MK_COMB (@lem4859503 _111544) (@lem4859502 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859505 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : ((term236 _111541 _111543 _111544 y x f g s) = (term237 _111541 _111543 _111544 y x f g s)) = ((term230 _111541 _111543 _111544 y x f g s) = (term253 _111541 _111543 _111544 y x f g s)).
Proof. exact (MK_COMB (@lem4859496 _111541 _111543 _111544 y x f g s) (@lem4859504 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859506 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term230 _111541 _111543 _111544 y x f g s) = (term253 _111541 _111543 _111544 y x f g s).
Proof. exact (EQ_MP (@lem4859505 _111541 _111543 _111544 y x f g s) (@lem4859483 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859507 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term232 _111541 _111543 _111544 x f g s) = (term254 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun y : _111543 => @lem4859506 _111541 _111543 _111544 y x f g s)). Qed.
Lemma lem4859508 {_111543 : Type'} : (@ex _111543) = (@ex _111543).
Proof. exact (eq_refl (@ex _111543)). Qed.
Lemma lem4859509 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term233 _111541 _111543 _111544 x f g s) = (term255 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859508 _111543) (@lem4859507 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859510 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term216 _111541 _111543 _111544 x f g s) = (term255 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859479 _111541 _111543 _111544 x f g s) (@lem4859509 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859512 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term149 _111541 _111543 _111544 x f g s) = (term255 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859453 _111541 _111543 _111544 x f g s) (@lem4859510 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859513 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term105 _111541 _111543 _111544 x f g s) = (term255 _111541 _111543 _111544 x f g s).
Proof. exact (TRANS (@lem4859089 _111541 _111543 _111544 x f g s) (@lem4859512 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859514 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term105 _111541 _111543 _111544 x f g s) : term255 _111541 _111543 _111544 x f g s.
Proof. exact (EQ_MP (@lem4859513 _111541 _111543 _111544 x f g s) (@lem4859005 _111541 _111543 _111544 x f g s h1)). Qed.
Lemma lem4859515 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term253 _111541 _111543 _111544 y x f g s) : term253 _111541 _111543 _111544 y x f g s.
Proof. exact (h1). Qed.
Lemma lem4859516 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term250 _111541 _111543 _111544 y x f g s x') : term250 _111541 _111543 _111544 y x f g s x'.
Proof. exact (h1). Qed.
Lemma lem4859531 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term77 _111541 _111543 _111544 x f g s x') = (term77 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term77 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859540 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term117 _111541 _111543 x f y) = (term117 _111541 _111543 x f y).
Proof. exact (eq_refl (term117 _111541 _111543 x f y)). Qed.
Lemma lem4859557 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term107 _111543 _111544 y g s x) = (term107 _111543 _111544 y g s x).
Proof. exact (eq_refl (term107 _111543 _111544 y g s x)). Qed.
Lemma lem4859558 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term115 _111543 _111544 y g s) = (term115 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4859557 _111543 _111544 y g s x)). Qed.
Lemma lem4859559 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859560 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term116 _111543 _111544 y g s) = (term116 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859559 _111544) (@lem4859558 _111543 _111544 y g s)). Qed.
Lemma lem4859561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859562 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term119 _111543 _111544 y g s) = (term119 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859561) (@lem4859560 _111543 _111544 y g s)). Qed.
Lemma lem4859563 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term121 _111541 _111543 _111544 g s x f y) = (term121 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859562 _111543 _111544 y g s) (@lem4859540 _111541 _111543 x f y)). Qed.
Lemma lem4859564 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term128 _111541 _111543 _111544 g s x f) = (term128 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859563 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859565 {_111543 : Type'} : (@all _111543) = (@all _111543).
Proof. exact (eq_refl (@all _111543)). Qed.
Lemma lem4859566 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term129 _111541 _111543 _111544 g s x f) = (term129 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859565 _111543) (@lem4859564 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4859568 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term140 _111541 _111543 _111544 g s x f) = (term140 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859567) (@lem4859566 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859569 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term212 _111541 _111543 _111544 x f g s x') = (term212 _111541 _111543 _111544 x f g s x').
Proof. exact (MK_COMB (@lem4859568 _111541 _111543 _111544 g s x f) (@lem4859531 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859588 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term131 _111541 _111543 _111544 x f g s x') = (term131 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term131 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859589 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term137 _111541 _111543 _111544 x f g s) = (term137 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859588 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859590 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859591 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859590 _111544) (@lem4859589 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859616 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term194 _111541 _111543 _111544 g s x' x f y) = (term194 _111541 _111543 _111544 g s x' x f y).
Proof. exact (eq_refl (term194 _111541 _111543 _111544 g s x' x f y)). Qed.
Lemma lem4859617 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term196 _111541 _111543 _111544 x' y x f g s) = (term196 _111541 _111543 _111544 x' y x f g s).
Proof. exact (MK_COMB (@lem4859616 _111541 _111543 _111544 g s x' x f y) (@lem4859591 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859619 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term248 _111541 _111543 _111544 x' y x f g s) = (term248 _111541 _111543 _111544 x' y x f g s).
Proof. exact (MK_COMB (@lem4859618) (@lem4859617 _111541 _111543 _111544 x' y x f g s)). Qed.
Lemma lem4859620 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term250 _111541 _111543 _111544 y x f g s x') = (term250 _111541 _111543 _111544 y x f g s x').
Proof. exact (MK_COMB (@lem4859619 _111541 _111543 _111544 x' y x f g s) (@lem4859569 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859621 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term250 _111541 _111543 _111544 y x f g s x') : term250 _111541 _111543 _111544 y x f g s x'.
Proof. exact (EQ_MP (@lem4859620 _111541 _111543 _111544 y x f g s x') (@lem4859516 _111541 _111543 _111544 y x f g s x' h1)). Qed.
Lemma lem4859622 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term196 _111541 _111543 _111544 x' y x f g s.
Proof. exact (h1). Qed.
Lemma lem4859623 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term212 _111541 _111543 _111544 x f g s x'.
Proof. exact (h1). Qed.
Lemma lem4859624 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term138 _111541 _111543 _111544 x f g s.
Proof. exact (proj2 (@lem4859622 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859625 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term162 _111541 _111543 _111544 g s x' x f y.
Proof. exact (proj1 (@lem4859622 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859627 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term42 _111543 _111544 y g s x'.
Proof. exact (proj1 (@lem4859625 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859630 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term77 _111541 _111543 _111544 x f g s x'.
Proof. exact (proj2 (@lem4859623 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4859631 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term129 _111541 _111543 _111544 g s x f.
Proof. exact (proj1 (@lem4859623 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4859641 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) : (term131 _111541 _111543 _111544 x f g s x') = (term131 _111541 _111543 _111544 x f g s x').
Proof. exact (eq_refl (term131 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859642 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term137 _111541 _111543 _111544 x f g s) = (term137 _111541 _111543 _111544 x f g s).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859641 _111541 _111543 _111544 x f g s x')). Qed.
Lemma lem4859643 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859645 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term138 _111541 _111543 _111544 x f g s) = (term138 _111541 _111543 _111544 x f g s).
Proof. exact (MK_COMB (@lem4859643 _111544) (@lem4859642 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4859646 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term138 _111541 _111543 _111544 x f g s.
Proof. exact (EQ_MP (@lem4859645 _111541 _111543 _111544 x f g s) (@lem4859624 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859660 {A : Type'} (P : A -> Prop) (Q : Prop) : (term256 A P Q) = (term257 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4859661 {_111544 : Type'} (P : _111544 -> Prop) (Q : Prop) : (term256 _111544 P Q) = (term257 _111544 P Q).
Proof. exact (@lem4859660 _111544 P Q). Qed.
Lemma lem4859662 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term258 _111541 _111543 _111544 g s x f y) = (term259 _111541 _111543 _111544 g s x f y).
Proof. exact (@lem4859661 _111544 (term115 _111543 _111544 y g s) (term117 _111541 _111543 x f y)). Qed.
Lemma lem4859663 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term260 _111543 _111544 y g s x) = (term107 _111543 _111544 y g s x).
Proof. exact (eq_refl (term260 _111543 _111544 y g s x)). Qed.
Lemma lem4859664 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term261 _111543 _111544 y g s) = (term115 _111543 _111544 y g s).
Proof. exact (fun_ext (fun x : _111544 => @lem4859663 _111543 _111544 y g s x)). Qed.
Lemma lem4859665 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859666 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term262 _111543 _111544 y g s) = (term116 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859665 _111544) (@lem4859664 _111543 _111544 y g s)). Qed.
Lemma lem4859667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859668 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term263 _111543 _111544 y g s) = (term119 _111543 _111544 y g s).
Proof. exact (MK_COMB (@lem4859667) (@lem4859666 _111543 _111544 y g s)). Qed.
Lemma lem4859669 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term117 _111541 _111543 x f y) = (term117 _111541 _111543 x f y).
Proof. exact (eq_refl (term117 _111541 _111543 x f y)). Qed.
Lemma lem4859670 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term258 _111541 _111543 _111544 g s x f y) = (term121 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859668 _111543 _111544 y g s) (@lem4859669 _111541 _111543 x f y)). Qed.
Lemma lem4859671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859672 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term264 _111541 _111543 _111544 g s x f y) = (term265 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859671) (@lem4859670 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859673 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term260 _111543 _111544 y g s x) = (term107 _111543 _111544 y g s x).
Proof. exact (eq_refl (term260 _111543 _111544 y g s x)). Qed.
Lemma lem4859674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4859675 {_111543 _111544 : Type'} (y : _111543) (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) : (term266 _111543 _111544 y g s x) = (term267 _111543 _111544 y g s x).
Proof. exact (MK_COMB (@lem4859674) (@lem4859673 _111543 _111544 y g s x)). Qed.
Lemma lem4859676 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term117 _111541 _111543 x f y) = (term117 _111541 _111543 x f y).
Proof. exact (eq_refl (term117 _111541 _111543 x f y)). Qed.
Lemma lem4859677 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) (x' : _111541) (f : _111543 -> _111541) (y : _111543) : (term268 _111541 _111543 _111544 g s x x' f y) = (term269 _111541 _111543 _111544 g s x x' f y).
Proof. exact (MK_COMB (@lem4859675 _111543 _111544 y g s x) (@lem4859676 _111541 _111543 x' f y)). Qed.
Lemma lem4859678 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term270 _111541 _111543 _111544 g s x f y) = (term271 _111541 _111543 _111544 g s x f y).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859677 _111541 _111543 _111544 g s x' x f y)). Qed.
Lemma lem4859679 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859680 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term259 _111541 _111543 _111544 g s x f y) = (term272 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859679 _111544) (@lem4859678 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859681 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : ((term258 _111541 _111543 _111544 g s x f y) = (term259 _111541 _111543 _111544 g s x f y)) = ((term121 _111541 _111543 _111544 g s x f y) = (term272 _111541 _111543 _111544 g s x f y)).
Proof. exact (MK_COMB (@lem4859672 _111541 _111543 _111544 g s x f y) (@lem4859680 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859682 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term121 _111541 _111543 _111544 g s x f y) = (term272 _111541 _111543 _111544 g s x f y).
Proof. exact (EQ_MP (@lem4859681 _111541 _111543 _111544 g s x f y) (@lem4859662 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859683 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term128 _111541 _111543 _111544 g s x f) = (term273 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859682 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859684 {_111543 : Type'} : (@all _111543) = (@all _111543).
Proof. exact (eq_refl (@all _111543)). Qed.
Lemma lem4859685 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term129 _111541 _111543 _111544 g s x f) = (term274 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859684 _111543) (@lem4859683 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859698 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111544) (x' : _111541) (f : _111543 -> _111541) (y : _111543) : (term269 _111541 _111543 _111544 g s x x' f y) = (term269 _111541 _111543 _111544 g s x x' f y).
Proof. exact (eq_refl (term269 _111541 _111543 _111544 g s x x' f y)). Qed.
Lemma lem4859699 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term271 _111541 _111543 _111544 g s x f y) = (term271 _111541 _111543 _111544 g s x f y).
Proof. exact (fun_ext (fun x' : _111544 => @lem4859698 _111541 _111543 _111544 g s x' x f y)). Qed.
Lemma lem4859700 {_111544 : Type'} : (@all _111544) = (@all _111544).
Proof. exact (eq_refl (@all _111544)). Qed.
Lemma lem4859701 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term272 _111541 _111543 _111544 g s x f y) = (term272 _111541 _111543 _111544 g s x f y).
Proof. exact (MK_COMB (@lem4859700 _111544) (@lem4859699 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859702 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term273 _111541 _111543 _111544 g s x f) = (term273 _111541 _111543 _111544 g s x f).
Proof. exact (fun_ext (fun y : _111543 => @lem4859701 _111541 _111543 _111544 g s x f y)). Qed.
Lemma lem4859703 {_111543 : Type'} : (@all _111543) = (@all _111543).
Proof. exact (eq_refl (@all _111543)). Qed.
Lemma lem4859704 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term274 _111541 _111543 _111544 g s x f) = (term274 _111541 _111543 _111544 g s x f).
Proof. exact (MK_COMB (@lem4859703 _111543) (@lem4859702 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859705 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) : (term129 _111541 _111543 _111544 g s x f) = (term274 _111541 _111543 _111544 g s x f).
Proof. exact (TRANS (@lem4859685 _111541 _111543 _111544 g s x f) (@lem4859704 _111541 _111543 _111544 g s x f)). Qed.
Lemma lem4859706 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term274 _111541 _111543 _111544 g s x f.
Proof. exact (EQ_MP (@lem4859705 _111541 _111543 _111544 g s x f) (@lem4859631 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4859715 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term275 _111541 _111543 _111544 x f g s _60203.
Proof. exact (@lem4859646 _111541 _111543 _111544 x' y x f g s h1 _60203). Qed.
Lemma lem4859716 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term275 _111541 _111543 _111544 x f g s _60203) = (term131 _111541 _111543 _111544 x f g s _60203).
Proof. exact (eq_refl (term275 _111541 _111543 _111544 x f g s _60203)). Qed.
Lemma lem4859718 {_111541 _111543 _111544 : Type'} (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term276 _111541 _111543 _111544 g s x f _60204.
Proof. exact (@lem4859706 _111541 _111543 _111544 x f g s x' h1 _60204). Qed.
Lemma lem4859719 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (x : _111541) (f : _111543 -> _111541) (_60204 : _111543) : (term276 _111541 _111543 _111544 g s x f _60204) = (term272 _111541 _111543 _111544 g s x f _60204).
Proof. exact (eq_refl (term276 _111541 _111543 _111544 g s x f _60204)). Qed.
Lemma lem4859720 {_111541 _111543 _111544 : Type'} (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term272 _111541 _111543 _111544 g s x f _60204.
Proof. exact (EQ_MP (@lem4859719 _111541 _111543 _111544 g s x f _60204) (@lem4859718 _111541 _111543 _111544 _60204 x f g s x' h1)). Qed.
Lemma lem4859721 {_111541 _111543 _111544 : Type'} (_60204 : _111543) (_60205 : _111544) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term277 _111541 _111543 _111544 g s x f _60204 _60205.
Proof. exact (@lem4859720 _111541 _111543 _111544 _60204 x f g s x' h1 _60205). Qed.
Lemma lem4859722 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (_60205 : _111544) (x : _111541) (f : _111543 -> _111541) (_60204 : _111543) : (term277 _111541 _111543 _111544 g s x f _60204 _60205) = (term269 _111541 _111543 _111544 g s _60205 x f _60204).
Proof. exact (eq_refl (term277 _111541 _111543 _111544 g s x f _60204 _60205)). Qed.
Lemma lem4859723 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term269 _111541 _111543 _111544 g s _60205 x f _60204.
Proof. exact (EQ_MP (@lem4859722 _111541 _111543 _111544 g s _60205 x f _60204) (@lem4859721 _111541 _111543 _111544 _60204 _60205 x f g s x' h1)). Qed.
Lemma lem4859731 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : x = (f y).
Proof. exact (proj2 (@lem4859625 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859733 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : y = (g x').
Proof. exact (proj1 (@lem4859627 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859746 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (_60205 : _111544) (x : _111541) (f : _111543 -> _111541) (_60204 : _111543) : (term269 _111541 _111543 _111544 g s _60205 x f _60204) = (term278 _111541 _111543 _111544 g s _60205 x f _60204).
Proof. exact (@lem4858529 (term117 _111543 _111544 _60204 g _60205) (term279 _111544 s _60205) (term117 _111541 _111543 x f _60204)). Qed.
Lemma lem4859747 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term278 _111541 _111543 _111544 g s _60205 x f _60204.
Proof. exact (EQ_MP (@lem4859746 _111541 _111543 _111544 g s _60205 x f _60204) (@lem4859723 _111541 _111543 _111544 _60205 _60204 x f g s x' h1)). Qed.
Lemma lem4859749 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : x = (term70 _111541 _111543 _111544 f g x').
Proof. exact (proj1 (@lem4859630 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4859779 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term131 _111541 _111543 _111544 x f g s _60203.
Proof. exact (EQ_MP (@lem4859716 _111541 _111543 _111544 x f g s _60203) (@lem4859715 _111541 _111543 _111544 _60203 x' y x f g s h1)). Qed.
Lemma lem4859780 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) : (term280 _111541 _111543 x f) = (term280 _111541 _111543 x f).
Proof. exact (eq_refl (term280 _111541 _111543 x f)). Qed.
Lemma lem4859781 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : (term281 _111541 _111543 x f y) = (term282 _111541 _111543 _111544 x f g x').
Proof. exact (MK_COMB (@lem4859780 _111541 _111543 x f) (@lem4859733 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859782 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term282 _111541 _111543 _111544 x f g x') = (x = (term70 _111541 _111543 _111544 f g x')).
Proof. exact (eq_refl (term282 _111541 _111543 _111544 x f g x')). Qed.
Lemma lem4859783 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term283 _111541 _111543 x f y) = (term283 _111541 _111543 x f y).
Proof. exact (eq_refl (term283 _111541 _111543 x f y)). Qed.
Lemma lem4859784 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : ((term281 _111541 _111543 x f y) = (term282 _111541 _111543 _111544 x f g x')) = ((term281 _111541 _111543 x f y) = (x = (term70 _111541 _111543 _111544 f g x'))).
Proof. exact (MK_COMB (@lem4859783 _111541 _111543 x f y) (@lem4859782 _111541 _111543 _111544 x f g x')). Qed.
Lemma lem4859785 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term281 _111541 _111543 x f y) = (x = (f y)).
Proof. exact (eq_refl (term281 _111541 _111543 x f y)). Qed.
Lemma lem4859786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859787 {_111541 _111543 : Type'} (x : _111541) (f : _111543 -> _111541) (y : _111543) : (term283 _111541 _111543 x f y) = (term284 _111541 _111543 x f y).
Proof. exact (MK_COMB (@lem4859786) (@lem4859785 _111541 _111543 x f y)). Qed.
Lemma lem4859788 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (x = (term70 _111541 _111543 _111544 f g x')) = (x = (term70 _111541 _111543 _111544 f g x')).
Proof. exact (eq_refl (x = (term70 _111541 _111543 _111544 f g x'))). Qed.
Lemma lem4859789 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : ((term281 _111541 _111543 x f y) = (x = (term70 _111541 _111543 _111544 f g x'))) = ((x = (f y)) = (x = (term70 _111541 _111543 _111544 f g x'))).
Proof. exact (MK_COMB (@lem4859787 _111541 _111543 x f y) (@lem4859788 _111541 _111543 _111544 x f g x')). Qed.
Lemma lem4859790 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : ((term281 _111541 _111543 x f y) = (term282 _111541 _111543 _111544 x f g x')) = ((x = (f y)) = (x = (term70 _111541 _111543 _111544 f g x'))).
Proof. exact (TRANS (@lem4859784 _111541 _111543 _111544 y x f g x') (@lem4859789 _111541 _111543 _111544 y x f g x')). Qed.
Lemma lem4859791 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : (x = (f y)) = (x = (term70 _111541 _111543 _111544 f g x')).
Proof. exact (EQ_MP (@lem4859790 _111541 _111543 _111544 y x f g x') (@lem4859781 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859792 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : x = (term70 _111541 _111543 _111544 f g x').
Proof. exact (EQ_MP (@lem4859791 _111541 _111543 _111544 x' y x f g s h1) (@lem4859731 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859821 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term285 _111541 _111543 _111544 f g s _60203) = (term285 _111541 _111543 _111544 f g s _60203).
Proof. exact (eq_refl (term285 _111541 _111543 _111544 f g s _60203)). Qed.
Lemma lem4859822 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : (term286 _111541 _111543 _111544 f g s _60203 x) = (term287 _111541 _111543 _111544 s _60203 f g x').
Proof. exact (MK_COMB (@lem4859821 _111541 _111543 _111544 f g s _60203) (@lem4859792 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859823 {_111541 _111543 _111544 : Type'} (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term287 _111541 _111543 _111544 s _60203 f g x') = (term288 _111541 _111543 _111544 x' f g s _60203).
Proof. exact (eq_refl (term287 _111541 _111543 _111544 s _60203 f g x')). Qed.
Lemma lem4859824 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) (x : _111541) : (term289 _111541 _111543 _111544 f g s _60203 x) = (term289 _111541 _111543 _111544 f g s _60203 x).
Proof. exact (eq_refl (term289 _111541 _111543 _111544 f g s _60203 x)). Qed.
Lemma lem4859825 {_111541 _111543 _111544 : Type'} (x : _111541) (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : ((term286 _111541 _111543 _111544 f g s _60203 x) = (term287 _111541 _111543 _111544 s _60203 f g x')) = ((term286 _111541 _111543 _111544 f g s _60203 x) = (term288 _111541 _111543 _111544 x' f g s _60203)).
Proof. exact (MK_COMB (@lem4859824 _111541 _111543 _111544 f g s _60203 x) (@lem4859823 _111541 _111543 _111544 x' f g s _60203)). Qed.
Lemma lem4859826 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term286 _111541 _111543 _111544 f g s _60203 x) = (term131 _111541 _111543 _111544 x f g s _60203).
Proof. exact (eq_refl (term286 _111541 _111543 _111544 f g s _60203 x)). Qed.
Lemma lem4859827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859828 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term289 _111541 _111543 _111544 f g s _60203 x) = (term290 _111541 _111543 _111544 x f g s _60203).
Proof. exact (MK_COMB (@lem4859827) (@lem4859826 _111541 _111543 _111544 x f g s _60203)). Qed.
Lemma lem4859829 {_111541 _111543 _111544 : Type'} (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term288 _111541 _111543 _111544 x' f g s _60203) = (term288 _111541 _111543 _111544 x' f g s _60203).
Proof. exact (eq_refl (term288 _111541 _111543 _111544 x' f g s _60203)). Qed.
Lemma lem4859830 {_111541 _111543 _111544 : Type'} (x : _111541) (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : ((term286 _111541 _111543 _111544 f g s _60203 x) = (term288 _111541 _111543 _111544 x' f g s _60203)) = ((term131 _111541 _111543 _111544 x f g s _60203) = (term288 _111541 _111543 _111544 x' f g s _60203)).
Proof. exact (MK_COMB (@lem4859828 _111541 _111543 _111544 x f g s _60203) (@lem4859829 _111541 _111543 _111544 x' f g s _60203)). Qed.
Lemma lem4859831 {_111541 _111543 _111544 : Type'} (x : _111541) (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : ((term286 _111541 _111543 _111544 f g s _60203 x) = (term287 _111541 _111543 _111544 s _60203 f g x')) = ((term131 _111541 _111543 _111544 x f g s _60203) = (term288 _111541 _111543 _111544 x' f g s _60203)).
Proof. exact (TRANS (@lem4859825 _111541 _111543 _111544 x x' f g s _60203) (@lem4859830 _111541 _111543 _111544 x x' f g s _60203)). Qed.
Lemma lem4859832 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : (term131 _111541 _111543 _111544 x f g s _60203) = (term288 _111541 _111543 _111544 x' f g s _60203).
Proof. exact (EQ_MP (@lem4859831 _111541 _111543 _111544 x x' f g s _60203) (@lem4859822 _111541 _111543 _111544 _60203 x' y x f g s h1)). Qed.
Lemma lem4859833 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term288 _111541 _111543 _111544 x' f g s _60203.
Proof. exact (EQ_MP (@lem4859832 _111541 _111543 _111544 _60203 x' y x f g s h1) (@lem4859779 _111541 _111543 _111544 _60203 x' y x f g s h1)). Qed.
Lemma lem4859862 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (_60205 : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term291 _111541 _111543 _111544 g s _60205 f _60204) = (term291 _111541 _111543 _111544 g s _60205 f _60204).
Proof. exact (eq_refl (term291 _111541 _111543 _111544 g s _60205 f _60204)). Qed.
Lemma lem4859863 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : (term292 _111541 _111543 _111544 g s _60205 f _60204 x) = (term293 _111541 _111543 _111544 s _60205 _60204 f g x').
Proof. exact (MK_COMB (@lem4859862 _111541 _111543 _111544 g s _60205 f _60204) (@lem4859749 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4859864 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term293 _111541 _111543 _111544 s _60205 _60204 f g x') = (term294 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (eq_refl (term293 _111541 _111543 _111544 s _60205 _60204 f g x')). Qed.
Lemma lem4859865 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (_60205 : _111544) (f : _111543 -> _111541) (_60204 : _111543) (x : _111541) : (term295 _111541 _111543 _111544 g s _60205 f _60204 x) = (term295 _111541 _111543 _111544 g s _60205 f _60204 x).
Proof. exact (eq_refl (term295 _111541 _111543 _111544 g s _60205 f _60204 x)). Qed.
Lemma lem4859866 {_111541 _111543 _111544 : Type'} (x : _111541) (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : ((term292 _111541 _111543 _111544 g s _60205 f _60204 x) = (term293 _111541 _111543 _111544 s _60205 _60204 f g x')) = ((term292 _111541 _111543 _111544 g s _60205 f _60204 x) = (term294 _111541 _111543 _111544 s _60205 g x' f _60204)).
Proof. exact (MK_COMB (@lem4859865 _111541 _111543 _111544 g s _60205 f _60204 x) (@lem4859864 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4859867 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (_60205 : _111544) (x : _111541) (f : _111543 -> _111541) (_60204 : _111543) : (term292 _111541 _111543 _111544 g s _60205 f _60204 x) = (term278 _111541 _111543 _111544 g s _60205 x f _60204).
Proof. exact (eq_refl (term292 _111541 _111543 _111544 g s _60205 f _60204 x)). Qed.
Lemma lem4859868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4859869 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (_60205 : _111544) (x : _111541) (f : _111543 -> _111541) (_60204 : _111543) : (term295 _111541 _111543 _111544 g s _60205 f _60204 x) = (term296 _111541 _111543 _111544 g s _60205 x f _60204).
Proof. exact (MK_COMB (@lem4859868) (@lem4859867 _111541 _111543 _111544 g s _60205 x f _60204)). Qed.
Lemma lem4859870 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term294 _111541 _111543 _111544 s _60205 g x' f _60204) = (term294 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (eq_refl (term294 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4859871 {_111541 _111543 _111544 : Type'} (x : _111541) (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : ((term292 _111541 _111543 _111544 g s _60205 f _60204 x) = (term294 _111541 _111543 _111544 s _60205 g x' f _60204)) = ((term278 _111541 _111543 _111544 g s _60205 x f _60204) = (term294 _111541 _111543 _111544 s _60205 g x' f _60204)).
Proof. exact (MK_COMB (@lem4859869 _111541 _111543 _111544 g s _60205 x f _60204) (@lem4859870 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4859872 {_111541 _111543 _111544 : Type'} (x : _111541) (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : ((term292 _111541 _111543 _111544 g s _60205 f _60204 x) = (term293 _111541 _111543 _111544 s _60205 _60204 f g x')) = ((term278 _111541 _111543 _111544 g s _60205 x f _60204) = (term294 _111541 _111543 _111544 s _60205 g x' f _60204)).
Proof. exact (TRANS (@lem4859866 _111541 _111543 _111544 x s _60205 g x' f _60204) (@lem4859871 _111541 _111543 _111544 x s _60205 g x' f _60204)). Qed.
Lemma lem4859873 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : (term278 _111541 _111543 _111544 g s _60205 x f _60204) = (term294 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (EQ_MP (@lem4859872 _111541 _111543 _111544 x s _60205 g x' f _60204) (@lem4859863 _111541 _111543 _111544 _60205 _60204 x f g s x' h1)). Qed.
Lemma lem4859874 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term294 _111541 _111543 _111544 s _60205 g x' f _60204.
Proof. exact (EQ_MP (@lem4859873 _111541 _111543 _111544 _60205 _60204 x f g s x' h1) (@lem4859747 _111541 _111543 _111544 _60205 _60204 x f g s x' h1)). Qed.
Lemma lem4859924 {_111541 : Type'} (x : _111541) : x = x.
Proof. exact (@lem21386 _111541 x). Qed.
Lemma lem4859925 {_111541 : Type'} (x : _111541) : x = x.
Proof. exact (@lem4859924 _111541 x). Qed.
Lemma lem4859926 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x').
Proof. exact (@lem4859925 _111541 (term70 _111541 _111543 _111544 f g x')). Qed.
Lemma lem4859927 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : term297 _111541 _111543 _111544 f g x'.
Proof. exact (fun h0 : term298 _111541 _111543 _111544 f g x' => @lem4859926 _111541 _111543 _111544 f g x'). Qed.
Lemma lem4859929 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4859930 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term297 _111541 _111543 _111544 f g x') = ((term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x')).
Proof. exact (@lem4859929 ((term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x'))). Qed.
Lemma lem4859931 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x').
Proof. exact (EQ_MP (@lem4859930 _111541 _111543 _111544 f g x') (@lem4859927 _111541 _111543 _111544 f g x')). Qed.
Lemma lem4859933 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : s x'.
Proof. exact (proj2 (@lem4859627 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859934 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term300 _111544 s x'.
Proof. exact (fun h0 : term279 _111544 s x' => @lem4859933 _111541 _111543 _111544 x' y x f g s h1). Qed.
Lemma lem4859936 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4859937 {_111544 : Type'} (s : _111544 -> Prop) (x' : _111544) : (term300 _111544 s x') = (s x').
Proof. exact (@lem4859936 (s x')). Qed.
Lemma lem4859938 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : s x'.
Proof. exact (EQ_MP (@lem4859937 _111544 s x') (@lem4859934 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859940 (a : Prop) (b : Prop) : (term301 a b) = (term302 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4859941 {_111541 _111543 _111544 : Type'} (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term288 _111541 _111543 _111544 x' f g s _60203) = (term303 _111541 _111543 _111544 x' f g s _60203).
Proof. exact (@lem4859940 ((term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g _60203)) (s _60203)). Qed.
Lemma lem4859943 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4859944 {_111541 _111543 _111544 : Type'} (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term303 _111541 _111543 _111544 x' f g s _60203) = (term304 _111541 _111543 _111544 x' f g s _60203).
Proof. exact (@lem4859943 (term305 _111541 _111543 _111544 x' f g s _60203)). Qed.
Lemma lem4859945 {_111541 _111543 _111544 : Type'} (x' : _111544) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (_60203 : _111544) : (term288 _111541 _111543 _111544 x' f g s _60203) = (term304 _111541 _111543 _111544 x' f g s _60203).
Proof. exact (TRANS (@lem4859941 _111541 _111543 _111544 x' f g s _60203) (@lem4859944 _111541 _111543 _111544 x' f g s _60203)). Qed.
Lemma lem4859947 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term306 _111541 _111543 _111544 f g s x'.
Proof. exact (conj (@lem4859931 _111541 _111543 _111544 f g x') (@lem4859938 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859949 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term304 _111541 _111543 _111544 x' f g s _60203.
Proof. exact (EQ_MP (@lem4859945 _111541 _111543 _111544 x' f g s _60203) (@lem4859833 _111541 _111543 _111544 _60203 x' y x f g s h1)). Qed.
Lemma lem4859950 {_111541 _111543 _111544 : Type'} (_60203 : _111544) (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term304 _111541 _111543 _111544 x' f g s _60203.
Proof. exact (@lem4859949 _111541 _111543 _111544 _60203 x' y x f g s h1). Qed.
Lemma lem4859951 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term307 _111541 _111543 _111544 f g s x'.
Proof. exact (@lem4859950 _111541 _111543 _111544 x' x' y x f g s h1). Qed.
Lemma lem4859954 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : False.
Proof. exact (@lem4859951 _111541 _111543 _111544 x' y x f g s h1 (@lem4859947 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4859955 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : term308.
Proof. exact (fun h0 : ~ False => @lem4859954 _111541 _111543 _111544 x' y x f g s h1). Qed.
Lemma lem4859957 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4859958 : term308 = False.
Proof. exact (@lem4859957 False). Qed.
Lemma lem4859995 {_111543 : Type'} (x : _111543) : x = x.
Proof. exact (@lem21386 _111543 x). Qed.
Lemma lem4859996 {_111543 : Type'} (x : _111543) : x = x.
Proof. exact (@lem4859995 _111543 x). Qed.
Lemma lem4859997 {_111543 _111544 : Type'} (g : _111544 -> _111543) (x' : _111544) : (g x') = (g x').
Proof. exact (@lem4859996 _111543 (g x')). Qed.
Lemma lem4859998 {_111543 _111544 : Type'} (g : _111544 -> _111543) (x' : _111544) : term309 _111543 _111544 g x'.
Proof. exact (fun h0 : term310 _111543 _111544 g x' => @lem4859997 _111543 _111544 g x'). Qed.
Lemma lem4860000 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4860001 {_111543 _111544 : Type'} (g : _111544 -> _111543) (x' : _111544) : (term309 _111543 _111544 g x') = ((g x') = (g x')).
Proof. exact (@lem4860000 ((g x') = (g x'))). Qed.
Lemma lem4860002 {_111543 _111544 : Type'} (g : _111544 -> _111543) (x' : _111544) : (g x') = (g x').
Proof. exact (EQ_MP (@lem4860001 _111543 _111544 g x') (@lem4859998 _111543 _111544 g x')). Qed.
Lemma lem4860004 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : s x'.
Proof. exact (proj2 (@lem4859630 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4860005 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term300 _111544 s x'.
Proof. exact (fun h0 : term279 _111544 s x' => @lem4860004 _111541 _111543 _111544 x f g s x' h1). Qed.
Lemma lem4860007 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4860008 {_111544 : Type'} (s : _111544 -> Prop) (x' : _111544) : (term300 _111544 s x') = (s x').
Proof. exact (@lem4860007 (s x')). Qed.
Lemma lem4860009 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : s x'.
Proof. exact (EQ_MP (@lem4860008 _111544 s x') (@lem4860005 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4860011 {_111541 : Type'} (x : _111541) : x = x.
Proof. exact (@lem21386 _111541 x). Qed.
Lemma lem4860012 {_111541 : Type'} (x : _111541) : x = x.
Proof. exact (@lem4860011 _111541 x). Qed.
Lemma lem4860013 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x').
Proof. exact (@lem4860012 _111541 (term70 _111541 _111543 _111544 f g x')). Qed.
Lemma lem4860014 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : term297 _111541 _111543 _111544 f g x'.
Proof. exact (fun h0 : term298 _111541 _111543 _111544 f g x' => @lem4860013 _111541 _111543 _111544 f g x'). Qed.
Lemma lem4860016 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4860017 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term297 _111541 _111543 _111544 f g x') = ((term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x')).
Proof. exact (@lem4860016 ((term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x'))). Qed.
Lemma lem4860018 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (x' : _111544) : (term70 _111541 _111543 _111544 f g x') = (term70 _111541 _111543 _111544 f g x').
Proof. exact (EQ_MP (@lem4860017 _111541 _111543 _111544 f g x') (@lem4860014 _111541 _111543 _111544 f g x')). Qed.
Lemma lem4860020 (a : Prop) (b : Prop) : (term301 a b) = (term302 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4860021 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term311 _111541 _111543 _111544 s _60205 g x' f _60204) = (term312 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (@lem4860020 (s _60205) ((term70 _111541 _111543 _111544 f g x') = (f _60204))). Qed.
Lemma lem4860022 {_111543 _111544 : Type'} (_60204 : _111543) (g : _111544 -> _111543) (_60205 : _111544) : (term313 _111543 _111544 _60204 g _60205) = (term313 _111543 _111544 _60204 g _60205).
Proof. exact (eq_refl (term313 _111543 _111544 _60204 g _60205)). Qed.
Lemma lem4860023 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term294 _111541 _111543 _111544 s _60205 g x' f _60204) = (term314 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (MK_COMB (@lem4860022 _111543 _111544 _60204 g _60205) (@lem4860021 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4860025 (a : Prop) (b : Prop) : (term301 a b) = (term302 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4860026 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term314 _111541 _111543 _111544 s _60205 g x' f _60204) = (term315 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (@lem4860025 (_60204 = (g _60205)) (term316 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4860027 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term294 _111541 _111543 _111544 s _60205 g x' f _60204) = (term315 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (TRANS (@lem4860023 _111541 _111543 _111544 s _60205 g x' f _60204) (@lem4860026 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4860029 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4860030 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term315 _111541 _111543 _111544 s _60205 g x' f _60204) = (term317 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (@lem4860029 (term318 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4860031 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (_60205 : _111544) (g : _111544 -> _111543) (x' : _111544) (f : _111543 -> _111541) (_60204 : _111543) : (term294 _111541 _111543 _111544 s _60205 g x' f _60204) = (term317 _111541 _111543 _111544 s _60205 g x' f _60204).
Proof. exact (TRANS (@lem4860027 _111541 _111543 _111544 s _60205 g x' f _60204) (@lem4860030 _111541 _111543 _111544 s _60205 g x' f _60204)). Qed.
Lemma lem4860033 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term319 _111541 _111543 _111544 s f g x'.
Proof. exact (conj (@lem4860009 _111541 _111543 _111544 x f g s x' h1) (@lem4860018 _111541 _111543 _111544 f g x')). Qed.
Lemma lem4860034 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term320 _111541 _111543 _111544 s f g x'.
Proof. exact (conj (@lem4860002 _111543 _111544 g x') (@lem4860033 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4860036 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term317 _111541 _111543 _111544 s _60205 g x' f _60204.
Proof. exact (EQ_MP (@lem4860031 _111541 _111543 _111544 s _60205 g x' f _60204) (@lem4859874 _111541 _111543 _111544 _60205 _60204 x f g s x' h1)). Qed.
Lemma lem4860037 {_111541 _111543 _111544 : Type'} (_60205 : _111544) (_60204 : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term317 _111541 _111543 _111544 s _60205 g x' f _60204.
Proof. exact (@lem4860036 _111541 _111543 _111544 _60205 _60204 x f g s x' h1). Qed.
Lemma lem4860038 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term321 _111541 _111543 _111544 s f g x'.
Proof. exact (@lem4860037 _111541 _111543 _111544 x' (g x') x f g s x' h1). Qed.
Lemma lem4860041 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : False.
Proof. exact (@lem4860038 _111541 _111543 _111544 x f g s x' h1 (@lem4860034 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4860042 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : term308.
Proof. exact (fun h0 : ~ False => @lem4860041 _111541 _111543 _111544 x f g s x' h1). Qed.
Lemma lem4860044 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4860045 : term308 = False.
Proof. exact (@lem4860044 False). Qed.
Lemma lem4860047 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term212 _111541 _111543 _111544 x f g s x') : False.
Proof. exact (EQ_MP (@lem4860045) (@lem4860042 _111541 _111543 _111544 x f g s x' h1)). Qed.
Lemma lem4860049 {_111541 _111543 _111544 : Type'} (x' : _111544) (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term196 _111541 _111543 _111544 x' y x f g s) : False.
Proof. exact (EQ_MP (@lem4859958) (@lem4859955 _111541 _111543 _111544 x' y x f g s h1)). Qed.
Lemma lem4860050 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term250 _111541 _111543 _111544 y x f g s x') : False.
Proof. exact (or_elim (@lem4859621 _111541 _111543 _111544 y x f g s x' h1) (fun h0 : term196 _111541 _111543 _111544 x' y x f g s => @lem4860049 _111541 _111543 _111544 x' y x f g s h0) (fun h0 : term212 _111541 _111543 _111544 x f g s x' => @lem4860047 _111541 _111543 _111544 x f g s x' h0)). Qed.
Lemma lem4860051 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term250 _111541 _111543 _111544 y x f g s x') : (term250 _111541 _111543 _111544 y x f g s x') = False.
Proof. exact (prop_ext (fun h2 : term250 _111541 _111543 _111544 y x f g s x' => @lem4860050 _111541 _111543 _111544 y x f g s x' h1) (fun h2 : False => @lem4859621 _111541 _111543 _111544 y x f g s x' h1)). Qed.
Lemma lem4860052 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (x' : _111544) (h1 : term250 _111541 _111543 _111544 y x f g s x') : False.
Proof. exact (EQ_MP (@lem4860051 _111541 _111543 _111544 y x f g s x' h1) (@lem4859621 _111541 _111543 _111544 y x f g s x' h1)). Qed.
Lemma lem4860053 {_111541 _111543 _111544 : Type'} (y : _111543) (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term253 _111541 _111543 _111544 y x f g s) : False.
Proof. exact (ex_elim (@lem4859515 _111541 _111543 _111544 y x f g s h1) (fun x' : _111544 => fun h0 : term252 _111541 _111543 _111544 y x f g s x' => @lem4860052 _111541 _111543 _111544 y x f g s x' h0)). Qed.
Lemma lem4860054 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term105 _111541 _111543 _111544 x f g s) : False.
Proof. exact (ex_elim (@lem4859514 _111541 _111543 _111544 x f g s h1) (fun y : _111543 => fun h0 : term254 _111541 _111543 _111544 x f g s y => @lem4860053 _111541 _111543 _111544 y x f g s h0)). Qed.
Lemma lem4860055 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term105 _111541 _111543 _111544 x f g s) : (term105 _111541 _111543 _111544 x f g s) = False.
Proof. exact (prop_ext (fun h2 : term105 _111541 _111543 _111544 x f g s => @lem4860054 _111541 _111543 _111544 x f g s h1) (fun h2 : False => @lem4859005 _111541 _111543 _111544 x f g s h1)). Qed.
Lemma lem4860056 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term105 _111541 _111543 _111544 x f g s) : False.
Proof. exact (EQ_MP (@lem4860055 _111541 _111543 _111544 x f g s h1) (@lem4859005 _111541 _111543 _111544 x f g s h1)). Qed.
Lemma lem4860057 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term104 _111541 _111543 _111544 x f g s.
Proof. exact (fun h0 : term105 _111541 _111543 _111544 x f g s => @lem4860056 _111541 _111543 _111544 x f g s h0). Qed.
Lemma lem4860058 {_111541 _111543 _111544 : Type'} (x : _111541) (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term62 _111541 _111543 _111544 g s x f) = (term80 _111541 _111543 _111544 x f g s).
Proof. exact (EQ_MP (@lem4859004 _111541 _111543 _111544 x f g s) (@lem4860057 _111541 _111543 _111544 x f g s)). Qed.
Lemma lem4860063 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term83 _111541 _111543 _111544 f g s.
Proof. exact (fun x : _111541 => @lem4860058 _111541 _111543 _111544 x f g s). Qed.
Lemma lem4860068 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : term95 _111541 _111543 _111544 g s.
Proof. exact (fun f : _111543 -> _111541 => @lem4860063 _111541 _111543 _111544 f g s). Qed.
Lemma lem4860073 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : term99 _111541 _111543 _111544 s.
Proof. exact (fun g : _111544 -> _111543 => @lem4860068 _111541 _111543 _111544 g s). Qed.
Lemma lem4860078 {_111541 _111543 _111544 : Type'} : term103 _111541 _111543 _111544.
Proof. exact (fun s : _111544 -> Prop => @lem4860073 _111541 _111543 _111544 s). Qed.
Lemma lem4860079 {_111541 _111543 _111544 : Type'} : term102 _111541 _111543 _111544.
Proof. exact (EQ_MP (@lem4859000 _111541 _111543 _111544) (@lem4860078 _111541 _111543 _111544)). Qed.
Lemma lem4860080 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : term322 _111541 _111543 _111544 s.
Proof. exact (@lem4860079 _111541 _111543 _111544 s). Qed.
Lemma lem4860081 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : (term322 _111541 _111543 _111544 s) = (term98 _111541 _111543 _111544 s).
Proof. exact (eq_refl (term322 _111541 _111543 _111544 s)). Qed.
Lemma lem4860082 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) : term98 _111541 _111543 _111544 s.
Proof. exact (EQ_MP (@lem4860081 _111541 _111543 _111544 s) (@lem4860080 _111541 _111543 _111544 s)). Qed.
Lemma lem4860083 {_111541 _111543 _111544 : Type'} (s : _111544 -> Prop) (g : _111544 -> _111543) : term323 _111541 _111543 _111544 s g.
Proof. exact (@lem4860082 _111541 _111543 _111544 s g). Qed.
Lemma lem4860084 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : (term323 _111541 _111543 _111544 s g) = (term94 _111541 _111543 _111544 g s).
Proof. exact (eq_refl (term323 _111541 _111543 _111544 s g)). Qed.
Lemma lem4860085 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) : term94 _111541 _111543 _111544 g s.
Proof. exact (EQ_MP (@lem4860084 _111541 _111543 _111544 g s) (@lem4860083 _111541 _111543 _111544 s g)). Qed.
Lemma lem4860086 {_111541 _111543 _111544 : Type'} (g : _111544 -> _111543) (s : _111544 -> Prop) (f : _111543 -> _111541) : term324 _111541 _111543 _111544 g s f.
Proof. exact (@lem4860085 _111541 _111543 _111544 g s f). Qed.
Lemma lem4860087 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term324 _111541 _111543 _111544 g s f) = (term85 _111541 _111543 _111544 f g s).
Proof. exact (eq_refl (term324 _111541 _111543 _111544 g s f)). Qed.
Lemma lem4860088 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term85 _111541 _111543 _111544 f g s.
Proof. exact (EQ_MP (@lem4860087 _111541 _111543 _111544 f g s) (@lem4860086 _111541 _111543 _111544 g s f)). Qed.
Lemma lem4860090 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term85 _111541 _111543 _111544 f g s.
Proof. exact (@lem4858744 _111541 _111543 _111544 f g s (@lem4860088 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4860091 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term86 _111541 _111543 _111544 f g s) : False.
Proof. exact (@lem4860090 _111541 _111543 _111544 f g s (@lem4858728 _111541 _111543 _111544 f g s h1)). Qed.
Lemma lem4860092 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term86 _111541 _111543 _111544 f g s) : (term86 _111541 _111543 _111544 f g s) = False.
Proof. exact (prop_ext (fun h2 : term86 _111541 _111543 _111544 f g s => @lem4860091 _111541 _111543 _111544 f g s h1) (fun h2 : False => @lem4858728 _111541 _111543 _111544 f g s h1)). Qed.
Lemma lem4860093 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) (h1 : term86 _111541 _111543 _111544 f g s) : False.
Proof. exact (EQ_MP (@lem4860092 _111541 _111543 _111544 f g s h1) (@lem4858728 _111541 _111543 _111544 f g s h1)). Qed.
Lemma lem4860094 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term85 _111541 _111543 _111544 f g s.
Proof. exact (fun h0 : term86 _111541 _111543 _111544 f g s => @lem4860093 _111541 _111543 _111544 f g s h0). Qed.
Lemma lem4860095 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term83 _111541 _111543 _111544 f g s.
Proof. exact (EQ_MP (@lem4858727 _111541 _111543 _111544 f g s) (@lem4860094 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4860096 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : term10 _111541 _111543 _111544 f g s.
Proof. exact (EQ_MP (@lem4858723 _111541 _111543 _111544 f g s) (@lem4860095 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4860098 {_90072 : Type'} (s : type686 _90072) : term325 _90072 s.
Proof. exact (@lem3472199 _90072 s). Qed.
Lemma lem4860099 {_90072 : Type'} (s : type686 _90072) : (term325 _90072 s) = ((@INTERS _90072 s) = (term326 _90072 s)).
Proof. exact (eq_refl (term325 _90072 s)). Qed.
Lemma lem4860101 {_90107 : Type'} (s : type686 _90107) : term327 _90107 s.
Proof. exact (@lem3473248 _90107 s). Qed.
Lemma lem4860102 {_90107 : Type'} (s : type686 _90107) : (term327 _90107 s) = ((@UNIONS _90107 s) = (term328 _90107 s)).
Proof. exact (eq_refl (term327 _90107 s)). Qed.
Lemma lem4860104 {A : Type'} (P : type180 A) : term329 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4860105 {A : Type'} (P : type180 A) : (term329 A P) = (term330 A P).
Proof. exact (eq_refl (term329 A P)). Qed.
Lemma lem4860106 {A : Type'} (P : type180 A) : term330 A P.
Proof. exact (EQ_MP (@lem4860105 A P) (@lem4860104 A P)). Qed.
Lemma lem4860107 {A : Type'} (P : type180 A) (Q : type686 A) : term331 A P Q.
Proof. exact (@lem4860106 A P Q). Qed.
Lemma lem4860108 {A : Type'} (P : type180 A) (Q : type686 A) : (term331 A P Q) = ((@INTERSECTION_OF A P Q) = (term332 A P Q)).
Proof. exact (eq_refl (term331 A P Q)). Qed.
Lemma lem4860110 {A : Type'} (P : type180 A) : term333 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4860111 {A : Type'} (P : type180 A) : (term333 A P) = (term334 A P).
Proof. exact (eq_refl (term333 A P)). Qed.
Lemma lem4860112 {A : Type'} (P : type180 A) : term334 A P.
Proof. exact (EQ_MP (@lem4860111 A P) (@lem4860110 A P)). Qed.
Lemma lem4860113 {A : Type'} (P : type180 A) (Q : type686 A) : term335 A P Q.
Proof. exact (@lem4860112 A P Q). Qed.
Lemma lem4860114 {A : Type'} (P : type180 A) (Q : type686 A) : (term335 A P Q) = ((@UNION_OF A P Q) = (term336 A P Q)).
Proof. exact (eq_refl (term335 A P Q)). Qed.
Lemma lem4860119 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem4860114 A P Q) (@lem4860113 A P Q)). Qed.
Lemma lem4860120 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term336 A P Q).
Proof. exact (@lem4860119 A P Q). Qed.
Lemma lem4860121 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term337 A P).
Proof. exact (@lem4860120 A (@ARBITRARY A) P). Qed.
Lemma lem4860138 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4860139 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term338 A P s).
Proof. exact (MK_COMB (@lem4860121 A P) (@lem4860138 A s)). Qed.
Lemma lem4860141 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860142 {A : Type'} (f : type686 A) (y : A -> Prop) : (term339 A f y) = (f y).
Proof. exact (@lem4860141 (A -> Prop) Prop f y). Qed.
Lemma lem4860143 {A : Type'} (P : type686 A) (s : A -> Prop) : (term340 A P s) = (term338 A P s).
Proof. exact (@lem4860142 A (term337 A P) s). Qed.
Lemma lem4860144 {A : Type'} (P : type686 A) (s : A -> Prop) : (term338 A P s) = (term341 A P s).
Proof. exact (eq_refl (term338 A P s)). Qed.
Lemma lem4860145 {A : Type'} (P : type686 A) : (term342 A P) = (term337 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860144 A P s)). Qed.
Lemma lem4860146 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4860147 {A : Type'} (P : type686 A) (s : A -> Prop) : (term340 A P s) = (term338 A P s).
Proof. exact (MK_COMB (@lem4860145 A P) (@lem4860146 A s)). Qed.
Lemma lem4860148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4860149 {A : Type'} (P : type686 A) (s : A -> Prop) : (term343 A P s) = (term344 A P s).
Proof. exact (MK_COMB (@lem4860148) (@lem4860147 A P s)). Qed.
Lemma lem4860150 {A : Type'} (P : type686 A) (s : A -> Prop) : (term338 A P s) = (term341 A P s).
Proof. exact (eq_refl (term338 A P s)). Qed.
Lemma lem4860151 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term340 A P s) = (term338 A P s)) = ((term338 A P s) = (term341 A P s)).
Proof. exact (MK_COMB (@lem4860149 A P s) (@lem4860150 A P s)). Qed.
Lemma lem4860152 {A : Type'} (P : type686 A) (s : A -> Prop) : (term338 A P s) = (term341 A P s).
Proof. exact (EQ_MP (@lem4860151 A P s) (@lem4860143 A P s)). Qed.
Lemma lem4860169 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term341 A P s).
Proof. exact (TRANS (@lem4860139 A P s) (@lem4860152 A P s)). Qed.
Lemma lem4860170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4860171 {A : Type'} (P : type686 A) (s : A -> Prop) : (term345 A P s) = (term346 A P s).
Proof. exact (MK_COMB (@lem4860170) (@lem4860169 A P s)). Qed.
Lemma lem4860173 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem4860108 A P Q) (@lem4860107 A P Q)). Qed.
Lemma lem4860174 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term332 A P Q).
Proof. exact (@lem4860173 A P Q). Qed.
Lemma lem4860175 {A : Type'} (P : type686 A) : (term347 A P) = (term348 A P).
Proof. exact (@lem4860174 A (@ARBITRARY A) (term349 A P)). Qed.
Lemma lem4860191 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860192 {A : Type'} (f : type686 A) (y : A -> Prop) : (term339 A f y) = (f y).
Proof. exact (@lem4860191 (A -> Prop) Prop f y). Qed.
Lemma lem4860193 {A : Type'} (P : type686 A) (c : A -> Prop) : (term350 A P c) = (term351 A P c).
Proof. exact (@lem4860192 A (term349 A P) c). Qed.
Lemma lem4860194 {A : Type'} (P : type686 A) (s : A -> Prop) : (term351 A P s) = (term352 A P s).
Proof. exact (eq_refl (term351 A P s)). Qed.
Lemma lem4860195 {A : Type'} (P : type686 A) : (term353 A P) = (term349 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860194 A P s)). Qed.
Lemma lem4860196 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4860197 {A : Type'} (P : type686 A) (c : A -> Prop) : (term350 A P c) = (term351 A P c).
Proof. exact (MK_COMB (@lem4860195 A P) (@lem4860196 A c)). Qed.
Lemma lem4860198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4860199 {A : Type'} (P : type686 A) (c : A -> Prop) : (term354 A P c) = (term355 A P c).
Proof. exact (MK_COMB (@lem4860198) (@lem4860197 A P c)). Qed.
Lemma lem4860200 {A : Type'} (P : type686 A) (c : A -> Prop) : (term351 A P c) = (term352 A P c).
Proof. exact (eq_refl (term351 A P c)). Qed.
Lemma lem4860201 {A : Type'} (P : type686 A) (c : A -> Prop) : ((term350 A P c) = (term351 A P c)) = ((term351 A P c) = (term352 A P c)).
Proof. exact (MK_COMB (@lem4860199 A P c) (@lem4860200 A P c)). Qed.
Lemma lem4860202 {A : Type'} (P : type686 A) (c : A -> Prop) : (term351 A P c) = (term352 A P c).
Proof. exact (EQ_MP (@lem4860201 A P c) (@lem4860193 A P c)). Qed.
Lemma lem4860203 {A : Type'} (c : A -> Prop) (u : type686 A) : (term356 A c u) = (term356 A c u).
Proof. exact (eq_refl (term356 A c u)). Qed.
Lemma lem4860204 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term357 A u P c) = (term358 A u P c).
Proof. exact (MK_COMB (@lem4860203 A c u) (@lem4860202 A P c)). Qed.
Lemma lem4860207 {A : Type'} (u : type686 A) (P : type686 A) : (term359 A u P) = (term360 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4860204 A u P c)). Qed.
Lemma lem4860208 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860209 {A : Type'} (u : type686 A) (P : type686 A) : (term361 A u P) = (term362 A u P).
Proof. exact (MK_COMB (@lem4860208 A) (@lem4860207 A u P)). Qed.
Lemma lem4860214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4860215 {A : Type'} (u : type686 A) (P : type686 A) : (term363 A u P) = (term364 A u P).
Proof. exact (MK_COMB (@lem4860214) (@lem4860209 A u P)). Qed.
Lemma lem4860218 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@INTERS A u) = s) = ((@INTERS A u) = s).
Proof. exact (eq_refl ((@INTERS A u) = s)). Qed.
Lemma lem4860219 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term365 A P u s) = (term366 A P u s).
Proof. exact (MK_COMB (@lem4860215 A u P) (@lem4860218 A u s)). Qed.
Lemma lem4860222 {A : Type'} (u : type686 A) : (term367 A u) = (term367 A u).
Proof. exact (eq_refl (term367 A u)). Qed.
Lemma lem4860223 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term368 A P u s) = (term369 A P u s).
Proof. exact (MK_COMB (@lem4860222 A u) (@lem4860219 A P u s)). Qed.
Lemma lem4860226 {A : Type'} (P : type686 A) (s : A -> Prop) : (term370 A P s) = (term371 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4860223 A P u s)). Qed.
Lemma lem4860227 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4860228 {A : Type'} (P : type686 A) (s : A -> Prop) : (term372 A P s) = (term373 A P s).
Proof. exact (MK_COMB (@lem4860227 A) (@lem4860226 A P s)). Qed.
Lemma lem4860233 {A : Type'} (P : type686 A) : (term348 A P) = (term374 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860228 A P s)). Qed.
Lemma lem4860234 {A : Type'} (P : type686 A) : (term347 A P) = (term374 A P).
Proof. exact (TRANS (@lem4860175 A P) (@lem4860233 A P)). Qed.
Lemma lem4860235 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860236 {A : Type'} (P : type686 A) (s : A -> Prop) : (term375 A P s) = (term376 A P s).
Proof. exact (MK_COMB (@lem4860234 A P) (@lem4860235 A s)). Qed.
Lemma lem4860238 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860239 {A : Type'} (f : type686 A) (y : A -> Prop) : (term339 A f y) = (f y).
Proof. exact (@lem4860238 (A -> Prop) Prop f y). Qed.
Lemma lem4860240 {A : Type'} (P : type686 A) (s : A -> Prop) : (term377 A P s) = (term376 A P s).
Proof. exact (@lem4860239 A (term374 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860241 {A : Type'} (P : type686 A) (s : A -> Prop) : (term378 A P s) = (term373 A P s).
Proof. exact (eq_refl (term378 A P s)). Qed.
Lemma lem4860242 {A : Type'} (P : type686 A) : (term379 A P) = (term374 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860241 A P s)). Qed.
Lemma lem4860243 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860244 {A : Type'} (P : type686 A) (s : A -> Prop) : (term377 A P s) = (term376 A P s).
Proof. exact (MK_COMB (@lem4860242 A P) (@lem4860243 A s)). Qed.
Lemma lem4860245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4860246 {A : Type'} (P : type686 A) (s : A -> Prop) : (term380 A P s) = (term381 A P s).
Proof. exact (MK_COMB (@lem4860245) (@lem4860244 A P s)). Qed.
Lemma lem4860247 {A : Type'} (P : type686 A) (s : A -> Prop) : (term376 A P s) = (term382 A P s).
Proof. exact (eq_refl (term376 A P s)). Qed.
Lemma lem4860248 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term377 A P s) = (term376 A P s)) = ((term376 A P s) = (term382 A P s)).
Proof. exact (MK_COMB (@lem4860246 A P s) (@lem4860247 A P s)). Qed.
Lemma lem4860249 {A : Type'} (P : type686 A) (s : A -> Prop) : (term376 A P s) = (term382 A P s).
Proof. exact (EQ_MP (@lem4860248 A P s) (@lem4860240 A P s)). Qed.
Lemma lem4860266 {A : Type'} (P : type686 A) (s : A -> Prop) : (term375 A P s) = (term382 A P s).
Proof. exact (TRANS (@lem4860236 A P s) (@lem4860249 A P s)). Qed.
Lemma lem4860267 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@UNION_OF A (@ARBITRARY A) P s) = (term375 A P s)) = ((term341 A P s) = (term382 A P s)).
Proof. exact (MK_COMB (@lem4860171 A P s) (@lem4860266 A P s)). Qed.
Lemma lem4860270 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term341 A P s) = (term382 A P s)) = ((@UNION_OF A (@ARBITRARY A) P s) = (term375 A P s)).
Proof. exact (SYM (@lem4860267 A P s)). Qed.
Lemma lem4860271 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term341 A P s) : term341 A P s.
Proof. exact (h1). Qed.
Lemma lem4860272 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : term383 A P u s.
Proof. exact (h1). Qed.
Lemma lem4860273 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : term384 A P u s.
Proof. exact (h1). Qed.
Lemma lem4860275 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4860276 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term385 A u P.
Proof. exact (h1). Qed.
Lemma lem4860277 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term382 A P s) : term382 A P s.
Proof. exact (h1). Qed.
Lemma lem4860278 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : term386 A P u s.
Proof. exact (h1). Qed.
Lemma lem4860279 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : term387 A P u s.
Proof. exact (h1). Qed.
Lemma lem4860281 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (@INTERS A u) = (@DIFF A (@UNIV A) s).
Proof. exact (h1). Qed.
Lemma lem4860282 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term362 A u P.
Proof. exact (h1). Qed.
Lemma lem4860283 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4860284 {A : Type'} (s : A -> Prop) : (term388 A s) = ((term389 A s) = s).
Proof. exact (eq_refl (term388 A s)). Qed.
Lemma lem4860286 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term390 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4860287 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term390 _87967 _87968 P f) = (term391 _87967 _87968 P f).
Proof. exact (eq_refl (term390 _87967 _87968 P f)). Qed.
Lemma lem4860288 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term391 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4860287 _87967 _87968 P f) (@lem4860286 _87967 _87968 P f)). Qed.
Lemma lem4860289 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term392 _87967 _87968 P f s.
Proof. exact (@lem4860288 _87967 _87968 P f s). Qed.
Lemma lem4860290 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term392 _87967 _87968 P f s) = ((term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f)).
Proof. exact (eq_refl (term392 _87967 _87968 P f s)). Qed.
Lemma lem4860292 {A : Type'} (s : type686 A) : term395 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4860293 {A : Type'} (s : type686 A) : (term395 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term395 A s)). Qed.
Lemma lem4860297 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term396 A u P c.
Proof. exact (@lem4860276 A u P h1 c). Qed.
Lemma lem4860298 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term396 A u P c) = (term397 A u P c).
Proof. exact (eq_refl (term396 A u P c)). Qed.
Lemma lem4860299 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term397 A u P c.
Proof. exact (EQ_MP (@lem4860298 A u P c) (@lem4860297 A c u P h1)). Qed.
Lemma lem4860300 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4860301 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term385 A u P) (h2 : @IN (A -> Prop) c u) : P c.
Proof. exact (@lem4860299 A c u P h1 (@lem4860300 A c u h2)). Qed.
Lemma lem4860302 {A : Type'} (P : type686 A) (c : A -> Prop) : (P c) = ((P c) = True).
Proof. exact (@lem7 (P c)). Qed.
Lemma lem4860303 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term385 A u P) (h2 : @IN (A -> Prop) c u) : (P c) = True.
Proof. exact (EQ_MP (@lem4860302 A P c) (@lem4860301 A P c u h1 h2)). Qed.
Lemma lem4860312 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4860293 A s) (@lem4860292 A s)). Qed.
Lemma lem4860313 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4860312 A s). Qed.
Lemma lem4860314 {A : Type'} (u : type686 A) : (term398 A u) = True.
Proof. exact (@lem4860313 A (term399 A u)). Qed.
Lemma lem4860315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4860316 {A : Type'} (u : type686 A) : (term400 A u) = (and True).
Proof. exact (MK_COMB (@lem4860315) (@lem4860314 A u)). Qed.
Lemma lem4860320 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4860290 _87967 _87968 s P f) (@lem4860289 _87967 _87968 P f s)). Qed.
Lemma lem4860321 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term401 A f s P) = (term402 A s P f).
Proof. exact (@lem4860320 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4860322 {A : Type'} (u : type686 A) (P : type686 A) : (term403 A u P) = (term404 A u P).
Proof. exact (@lem4860321 A u (term349 A P) (term405 A)). Qed.
Lemma lem4860323 {A : Type'} (P : type686 A) (c : A -> Prop) : (term351 A P c) = (term352 A P c).
Proof. exact (eq_refl (term351 A P c)). Qed.
Lemma lem4860324 {A : Type'} (c : A -> Prop) (u : type686 A) : (term406 A c u) = (term406 A c u).
Proof. exact (eq_refl (term406 A c u)). Qed.
Lemma lem4860325 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term407 A u P c) = (term408 A u P c).
Proof. exact (MK_COMB (@lem4860324 A c u) (@lem4860323 A P c)). Qed.
Lemma lem4860326 {A : Type'} (u : type686 A) (P : type686 A) : (term409 A u P) = (term410 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4860325 A u P c)). Qed.
Lemma lem4860327 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860328 {A : Type'} (u : type686 A) (P : type686 A) : (term403 A u P) = (term411 A u P).
Proof. exact (MK_COMB (@lem4860327 A) (@lem4860326 A u P)). Qed.
Lemma lem4860329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4860330 {A : Type'} (u : type686 A) (P : type686 A) : (term412 A u P) = (term413 A u P).
Proof. exact (MK_COMB (@lem4860329) (@lem4860328 A u P)). Qed.
Lemma lem4860331 {A : Type'} (P : type686 A) (x : A -> Prop) : (term414 A P x) = (term415 A P x).
Proof. exact (eq_refl (term414 A P x)). Qed.
Lemma lem4860332 {A : Type'} (x : A -> Prop) (u : type686 A) : (term356 A x u) = (term356 A x u).
Proof. exact (eq_refl (term356 A x u)). Qed.
Lemma lem4860333 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) : (term416 A u P x) = (term417 A u P x).
Proof. exact (MK_COMB (@lem4860332 A x u) (@lem4860331 A P x)). Qed.
Lemma lem4860334 {A : Type'} (u : type686 A) (P : type686 A) : (term418 A u P) = (term419 A u P).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860333 A u P x)). Qed.
Lemma lem4860335 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860336 {A : Type'} (u : type686 A) (P : type686 A) : (term404 A u P) = (term420 A u P).
Proof. exact (MK_COMB (@lem4860335 A) (@lem4860334 A u P)). Qed.
Lemma lem4860337 {A : Type'} (u : type686 A) (P : type686 A) : ((term403 A u P) = (term404 A u P)) = ((term411 A u P) = (term420 A u P)).
Proof. exact (MK_COMB (@lem4860330 A u P) (@lem4860336 A u P)). Qed.
Lemma lem4860338 {A : Type'} (u : type686 A) (P : type686 A) : (term411 A u P) = (term420 A u P).
Proof. exact (EQ_MP (@lem4860337 A u P) (@lem4860322 A u P)). Qed.
Lemma lem4860346 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term421 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4860347 (p : Prop) (q : Prop) (p' : Prop) : term422 p q p'.
Proof. exact (fun q' : Prop => @lem4860346 p q p' q'). Qed.
Lemma lem4860348 (p : Prop) (q : Prop) : term423 p q.
Proof. exact (fun p' : Prop => @lem4860347 p q p'). Qed.
Lemma lem4860349 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) : term424 A u P x.
Proof. exact (@lem4860348 (@IN (A -> Prop) x u) (term415 A P x)). Qed.
Lemma lem4860350 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term425 A u P x p'.
Proof. exact (@lem4860349 A u P x p'). Qed.
Lemma lem4860351 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : (term425 A u P x p') = (term426 A u P x p').
Proof. exact (eq_refl (term425 A u P x p')). Qed.
Lemma lem4860352 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term426 A u P x p'.
Proof. exact (EQ_MP (@lem4860351 A u P x p') (@lem4860350 A u P x p')). Qed.
Lemma lem4860353 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term427 A u P x p' q'.
Proof. exact (@lem4860352 A u P x p' q'). Qed.
Lemma lem4860354 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : (term427 A u P x p' q') = (term428 A u P x p' q').
Proof. exact (eq_refl (term427 A u P x p' q')). Qed.
Lemma lem4860355 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term428 A u P x p' q'.
Proof. exact (EQ_MP (@lem4860354 A u P x p' q') (@lem4860353 A u P x p' q')). Qed.
Lemma lem4860356 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = (@IN (A -> Prop) x u).
Proof. exact (eq_refl (@IN (A -> Prop) x u)). Qed.
Lemma lem4860357 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term429 A P x u q'.
Proof. exact (@lem4860355 A u P x (@IN (A -> Prop) x u) q'). Qed.
Lemma lem4860358 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term430 A P x u q'.
Proof. exact (@lem4860357 A P x u q' (@lem4860356 A x u)). Qed.
Lemma lem4860359 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (h1). Qed.
Lemma lem4860360 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = ((@IN (A -> Prop) x u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) x u)). Qed.
Lemma lem4860363 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term431 A u P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4860303 A P c u h1 h0). Qed.
Lemma lem4860364 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term431 A u P c.
Proof. exact (@lem4860363 A c u P h1). Qed.
Lemma lem4860365 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term432 A u P x.
Proof. exact (@lem4860364 A (term433 A x) u P h1). Qed.
Lemma lem4860367 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860368 {A : Type'} (f : type672 A) (y : A -> Prop) : (term434 A f y) = (f y).
Proof. exact (@lem4860367 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4860369 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (@lem4860368 A (term405 A) x). Qed.
Lemma lem4860370 {A : Type'} (c : A -> Prop) : (term436 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term436 A c)). Qed.
Lemma lem4860371 {A : Type'} : (term437 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4860370 A c)). Qed.
Lemma lem4860372 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4860373 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (MK_COMB (@lem4860371 A) (@lem4860372 A x)). Qed.
Lemma lem4860374 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860375 {A : Type'} (x : A -> Prop) : (term438 A x) = (term439 A x).
Proof. exact (MK_COMB (@lem4860374 A) (@lem4860373 A x)). Qed.
Lemma lem4860376 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term436 A x)). Qed.
Lemma lem4860377 {A : Type'} (x : A -> Prop) : ((term435 A x) = (term436 A x)) = ((term436 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4860375 A x) (@lem4860376 A x)). Qed.
Lemma lem4860378 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4860377 A x) (@lem4860369 A x)). Qed.
Lemma lem4860379 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860380 {A : Type'} (x : A -> Prop) : (term433 A x) = (term389 A x).
Proof. exact (MK_COMB (@lem4860379 A) (@lem4860378 A x)). Qed.
Lemma lem4860382 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4860284 A s) (@lem4860283 A s)). Qed.
Lemma lem4860383 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4860382 A s). Qed.
Lemma lem4860384 {A : Type'} (x : A -> Prop) : (term389 A x) = x.
Proof. exact (@lem4860383 A x). Qed.
Lemma lem4860385 {A : Type'} (x : A -> Prop) : (term433 A x) = x.
Proof. exact (TRANS (@lem4860380 A x) (@lem4860384 A x)). Qed.
Lemma lem4860386 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem4860387 {A : Type'} (x : A -> Prop) : (term440 A x) = (@IN (A -> Prop) x).
Proof. exact (MK_COMB (@lem4860386 A) (@lem4860385 A x)). Qed.
Lemma lem4860388 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860389 {A : Type'} (x : A -> Prop) (u : type686 A) : (term441 A x u) = (@IN (A -> Prop) x u).
Proof. exact (MK_COMB (@lem4860387 A x) (@lem4860388 A u)). Qed.
Lemma lem4860391 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = True.
Proof. exact (EQ_MP (@lem4860360 A x u) (@lem4860359 A x u h1)). Qed.
Lemma lem4860392 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (term441 A x u) = True.
Proof. exact (TRANS (@lem4860389 A x u) (@lem4860391 A x u h1)). Qed.
Lemma lem4860393 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : True = (term441 A x u).
Proof. exact (SYM (@lem4860392 A x u h1)). Qed.
Lemma lem4860394 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : term441 A x u.
Proof. exact (EQ_MP (@lem4860393 A x u h1) (@lem0)). Qed.
Lemma lem4860395 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term385 A u P) (h2 : @IN (A -> Prop) x u) : (term415 A P x) = True.
Proof. exact (@lem4860365 A x u P h1 (@lem4860394 A x u h2)). Qed.
Lemma lem4860396 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term442 A u P x.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4860395 A P x u h1 h0). Qed.
Lemma lem4860397 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) : term443 A P x u.
Proof. exact (@lem4860358 A P x u True). Qed.
Lemma lem4860398 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term417 A u P x) = (term444 A x u).
Proof. exact (@lem4860397 A P x u (@lem4860396 A x u P h1)). Qed.
Lemma lem4860400 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4860401 {A : Type'} (x : A -> Prop) (u : type686 A) : (term444 A x u) = True.
Proof. exact (@lem4860400 (@IN (A -> Prop) x u)). Qed.
Lemma lem4860402 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term417 A u P x) = True.
Proof. exact (TRANS (@lem4860398 A x u P h1) (@lem4860401 A x u)). Qed.
Lemma lem4860403 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term419 A u P) = (term445 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860402 A x u P h1)). Qed.
Lemma lem4860404 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860405 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term420 A u P) = (term446 A).
Proof. exact (MK_COMB (@lem4860404 A) (@lem4860403 A u P h1)). Qed.
Lemma lem4860407 {A : Type'} (t : Prop) : (term447 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4860408 {A : Type'} (t : Prop) : (term448 A t) = t.
Proof. exact (@lem4860407 (A -> Prop) t). Qed.
Lemma lem4860409 {A : Type'} : (term446 A) = True.
Proof. exact (@lem4860408 A True). Qed.
Lemma lem4860410 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term420 A u P) = True.
Proof. exact (TRANS (@lem4860405 A u P h1) (@lem4860409 A)). Qed.
Lemma lem4860411 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term411 A u P) = True.
Proof. exact (TRANS (@lem4860338 A u P) (@lem4860410 A u P h1)). Qed.
Lemma lem4860412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4860413 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term449 A u P) = (and True).
Proof. exact (MK_COMB (@lem4860412) (@lem4860411 A u P h1)). Qed.
Lemma lem4860416 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term450 A u) = (@DIFF A (@UNIV A) s)) = ((term450 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (eq_refl ((term450 A u) = (@DIFF A (@UNIV A) s))). Qed.
Lemma lem4860417 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term451 A P u s) = (term452 A u s).
Proof. exact (MK_COMB (@lem4860413 A u P h1) (@lem4860416 A u s)). Qed.
Lemma lem4860419 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4860420 {A : Type'} (u : type686 A) (s : A -> Prop) : (term452 A u s) = ((term450 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (@lem4860419 ((term450 A u) = (@DIFF A (@UNIV A) s))). Qed.
Lemma lem4860423 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term451 A P u s) = ((term450 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (TRANS (@lem4860417 A s u P h1) (@lem4860420 A u s)). Qed.
Lemma lem4860424 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term453 A P u s) = (term452 A u s).
Proof. exact (MK_COMB (@lem4860316 A u) (@lem4860423 A s u P h1)). Qed.
Lemma lem4860426 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4860427 {A : Type'} (u : type686 A) (s : A -> Prop) : (term452 A u s) = ((term450 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (@lem4860426 ((term450 A u) = (@DIFF A (@UNIV A) s))). Qed.
Lemma lem4860430 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term453 A P u s) = ((term450 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (TRANS (@lem4860424 A s u P h1) (@lem4860427 A u s)). Qed.
Lemma lem4860431 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : ((term450 A u) = (@DIFF A (@UNIV A) s)) = (term453 A P u s).
Proof. exact (SYM (@lem4860430 A s u P h1)). Qed.
Lemma lem4860435 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term390 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4860436 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term390 _87967 _87968 P f) = (term391 _87967 _87968 P f).
Proof. exact (eq_refl (term390 _87967 _87968 P f)). Qed.
Lemma lem4860437 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term391 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4860436 _87967 _87968 P f) (@lem4860435 _87967 _87968 P f)). Qed.
Lemma lem4860438 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term392 _87967 _87968 P f s.
Proof. exact (@lem4860437 _87967 _87968 P f s). Qed.
Lemma lem4860439 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term392 _87967 _87968 P f s) = ((term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f)).
Proof. exact (eq_refl (term392 _87967 _87968 P f s)). Qed.
Lemma lem4860441 {A : Type'} (s : type686 A) : term395 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4860442 {A : Type'} (s : type686 A) : (term395 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term395 A s)). Qed.
Lemma lem4860446 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term454 A u P c.
Proof. exact (@lem4860282 A u P h1 c). Qed.
Lemma lem4860447 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term454 A u P c) = (term358 A u P c).
Proof. exact (eq_refl (term454 A u P c)). Qed.
Lemma lem4860448 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term358 A u P c.
Proof. exact (EQ_MP (@lem4860447 A u P c) (@lem4860446 A c u P h1)). Qed.
Lemma lem4860449 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4860450 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) c u) : term352 A P c.
Proof. exact (@lem4860448 A c u P h1 (@lem4860449 A c u h2)). Qed.
Lemma lem4860451 {A : Type'} (P : type686 A) (c : A -> Prop) : (term352 A P c) = ((term352 A P c) = True).
Proof. exact (@lem7 (term352 A P c)). Qed.
Lemma lem4860452 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) c u) : (term352 A P c) = True.
Proof. exact (EQ_MP (@lem4860451 A P c) (@lem4860450 A P c u h1 h2)). Qed.
Lemma lem4860461 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4860442 A s) (@lem4860441 A s)). Qed.
Lemma lem4860462 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4860461 A s). Qed.
Lemma lem4860463 {A : Type'} (u : type686 A) : (term398 A u) = True.
Proof. exact (@lem4860462 A (term399 A u)). Qed.
Lemma lem4860464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4860465 {A : Type'} (u : type686 A) : (term400 A u) = (and True).
Proof. exact (MK_COMB (@lem4860464) (@lem4860463 A u)). Qed.
Lemma lem4860469 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4860439 _87967 _87968 s P f) (@lem4860438 _87967 _87968 P f s)). Qed.
Lemma lem4860470 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term401 A f s P) = (term402 A s P f).
Proof. exact (@lem4860469 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4860471 {A : Type'} (u : type686 A) (P : type686 A) : (term455 A u P) = (term456 A u P).
Proof. exact (@lem4860470 A u P (term405 A)). Qed.
Lemma lem4860479 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term421 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4860480 (p : Prop) (q : Prop) (p' : Prop) : term422 p q p'.
Proof. exact (fun q' : Prop => @lem4860479 p q p' q'). Qed.
Lemma lem4860481 (p : Prop) (q : Prop) : term423 p q.
Proof. exact (fun p' : Prop => @lem4860480 p q p'). Qed.
Lemma lem4860482 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) : term457 A u P x.
Proof. exact (@lem4860481 (@IN (A -> Prop) x u) (term458 A P x)). Qed.
Lemma lem4860483 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term459 A u P x p'.
Proof. exact (@lem4860482 A u P x p'). Qed.
Lemma lem4860484 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : (term459 A u P x p') = (term460 A u P x p').
Proof. exact (eq_refl (term459 A u P x p')). Qed.
Lemma lem4860485 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term460 A u P x p'.
Proof. exact (EQ_MP (@lem4860484 A u P x p') (@lem4860483 A u P x p')). Qed.
Lemma lem4860486 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term461 A u P x p' q'.
Proof. exact (@lem4860485 A u P x p' q'). Qed.
Lemma lem4860487 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : (term461 A u P x p' q') = (term462 A u P x p' q').
Proof. exact (eq_refl (term461 A u P x p' q')). Qed.
Lemma lem4860488 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term462 A u P x p' q'.
Proof. exact (EQ_MP (@lem4860487 A u P x p' q') (@lem4860486 A u P x p' q')). Qed.
Lemma lem4860489 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = (@IN (A -> Prop) x u).
Proof. exact (eq_refl (@IN (A -> Prop) x u)). Qed.
Lemma lem4860490 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term463 A P x u q'.
Proof. exact (@lem4860488 A u P x (@IN (A -> Prop) x u) q'). Qed.
Lemma lem4860491 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term464 A P x u q'.
Proof. exact (@lem4860490 A P x u q' (@lem4860489 A x u)). Qed.
Lemma lem4860492 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (h1). Qed.
Lemma lem4860493 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = ((@IN (A -> Prop) x u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) x u)). Qed.
Lemma lem4860496 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860497 {A : Type'} (f : type672 A) (y : A -> Prop) : (term434 A f y) = (f y).
Proof. exact (@lem4860496 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4860498 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (@lem4860497 A (term405 A) x). Qed.
Lemma lem4860499 {A : Type'} (c : A -> Prop) : (term436 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term436 A c)). Qed.
Lemma lem4860500 {A : Type'} : (term437 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4860499 A c)). Qed.
Lemma lem4860501 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4860502 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (MK_COMB (@lem4860500 A) (@lem4860501 A x)). Qed.
Lemma lem4860503 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860504 {A : Type'} (x : A -> Prop) : (term438 A x) = (term439 A x).
Proof. exact (MK_COMB (@lem4860503 A) (@lem4860502 A x)). Qed.
Lemma lem4860505 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term436 A x)). Qed.
Lemma lem4860506 {A : Type'} (x : A -> Prop) : ((term435 A x) = (term436 A x)) = ((term436 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4860504 A x) (@lem4860505 A x)). Qed.
Lemma lem4860507 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4860506 A x) (@lem4860498 A x)). Qed.
Lemma lem4860508 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4860509 {A : Type'} (P : type686 A) (x : A -> Prop) : (term458 A P x) = (term352 A P x).
Proof. exact (MK_COMB (@lem4860508 A P) (@lem4860507 A x)). Qed.
Lemma lem4860511 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term465 A u P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4860452 A P c u h1 h0). Qed.
Lemma lem4860512 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term465 A u P c.
Proof. exact (@lem4860511 A c u P h1). Qed.
Lemma lem4860513 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term465 A u P x.
Proof. exact (@lem4860512 A x u P h1). Qed.
Lemma lem4860515 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = True.
Proof. exact (EQ_MP (@lem4860493 A x u) (@lem4860492 A x u h1)). Qed.
Lemma lem4860516 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : True = (@IN (A -> Prop) x u).
Proof. exact (SYM (@lem4860515 A x u h1)). Qed.
Lemma lem4860517 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (EQ_MP (@lem4860516 A x u h1) (@lem0)). Qed.
Lemma lem4860518 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) x u) : (term352 A P x) = True.
Proof. exact (@lem4860513 A x u P h1 (@lem4860517 A x u h2)). Qed.
Lemma lem4860519 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) x u) : (term458 A P x) = True.
Proof. exact (TRANS (@lem4860509 A P x) (@lem4860518 A P x u h1 h2)). Qed.
Lemma lem4860520 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term466 A u P x.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4860519 A P x u h1 h0). Qed.
Lemma lem4860521 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) : term467 A P x u.
Proof. exact (@lem4860491 A P x u True). Qed.
Lemma lem4860522 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term468 A u P x) = (term444 A x u).
Proof. exact (@lem4860521 A P x u (@lem4860520 A x u P h1)). Qed.
Lemma lem4860524 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4860525 {A : Type'} (x : A -> Prop) (u : type686 A) : (term444 A x u) = True.
Proof. exact (@lem4860524 (@IN (A -> Prop) x u)). Qed.
Lemma lem4860526 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term468 A u P x) = True.
Proof. exact (TRANS (@lem4860522 A x u P h1) (@lem4860525 A x u)). Qed.
Lemma lem4860527 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term469 A u P) = (term445 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860526 A x u P h1)). Qed.
Lemma lem4860528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860529 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term456 A u P) = (term446 A).
Proof. exact (MK_COMB (@lem4860528 A) (@lem4860527 A u P h1)). Qed.
Lemma lem4860531 {A : Type'} (t : Prop) : (term447 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4860532 {A : Type'} (t : Prop) : (term448 A t) = t.
Proof. exact (@lem4860531 (A -> Prop) t). Qed.
Lemma lem4860533 {A : Type'} : (term446 A) = True.
Proof. exact (@lem4860532 A True). Qed.
Lemma lem4860534 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term456 A u P) = True.
Proof. exact (TRANS (@lem4860529 A u P h1) (@lem4860533 A)). Qed.
Lemma lem4860535 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term455 A u P) = True.
Proof. exact (TRANS (@lem4860471 A u P) (@lem4860534 A u P h1)). Qed.
Lemma lem4860536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4860537 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term470 A u P) = (and True).
Proof. exact (MK_COMB (@lem4860536) (@lem4860535 A u P h1)). Qed.
Lemma lem4860540 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term471 A u) = s) = ((term471 A u) = s).
Proof. exact (eq_refl ((term471 A u) = s)). Qed.
Lemma lem4860541 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term472 A P u s) = (term473 A u s).
Proof. exact (MK_COMB (@lem4860537 A u P h1) (@lem4860540 A u s)). Qed.
Lemma lem4860543 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4860544 {A : Type'} (u : type686 A) (s : A -> Prop) : (term473 A u s) = ((term471 A u) = s).
Proof. exact (@lem4860543 ((term471 A u) = s)). Qed.
Lemma lem4860547 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term472 A P u s) = ((term471 A u) = s).
Proof. exact (TRANS (@lem4860541 A s u P h1) (@lem4860544 A u s)). Qed.
Lemma lem4860548 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term474 A P u s) = (term473 A u s).
Proof. exact (MK_COMB (@lem4860465 A u) (@lem4860547 A s u P h1)). Qed.
Lemma lem4860550 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4860551 {A : Type'} (u : type686 A) (s : A -> Prop) : (term473 A u s) = ((term471 A u) = s).
Proof. exact (@lem4860550 ((term471 A u) = s)). Qed.
Lemma lem4860554 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term474 A P u s) = ((term471 A u) = s).
Proof. exact (TRANS (@lem4860548 A s u P h1) (@lem4860551 A u s)). Qed.
Lemma lem4860555 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : ((term471 A u) = s) = (term474 A P u s).
Proof. exact (SYM (@lem4860554 A s u P h1)). Qed.
Lemma lem4860559 {_90072 : Type'} (s : type686 _90072) : (@INTERS _90072 s) = (term326 _90072 s).
Proof. exact (EQ_MP (@lem4860099 _90072 s) (@lem4860098 _90072 s)). Qed.
Lemma lem4860560 {A : Type'} (s : type686 A) : (@INTERS A s) = (term326 A s).
Proof. exact (@lem4860559 A s). Qed.
Lemma lem4860561 {A : Type'} (u : type686 A) : (term450 A u) = (term475 A u).
Proof. exact (@lem4860560 A (term399 A u)). Qed.
Lemma lem4860562 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860563 {A : Type'} (u : type686 A) : (term476 A u) = (term477 A u).
Proof. exact (MK_COMB (@lem4860562 A) (@lem4860561 A u)). Qed.
Lemma lem4860564 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860565 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term450 A u) = (@DIFF A (@UNIV A) s)) = ((term475 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (MK_COMB (@lem4860563 A u) (@lem4860564 A s)). Qed.
Lemma lem4860566 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term475 A u) = (@DIFF A (@UNIV A) s)) = ((term450 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (SYM (@lem4860565 A u s)). Qed.
Lemma lem4860570 {_90107 : Type'} (s : type686 _90107) : (@UNIONS _90107 s) = (term328 _90107 s).
Proof. exact (EQ_MP (@lem4860102 _90107 s) (@lem4860101 _90107 s)). Qed.
Lemma lem4860571 {A : Type'} (s : type686 A) : (@UNIONS A s) = (term328 A s).
Proof. exact (@lem4860570 A s). Qed.
Lemma lem4860572 {A : Type'} (u : type686 A) : (term471 A u) = (term478 A u).
Proof. exact (@lem4860571 A (term399 A u)). Qed.
Lemma lem4860573 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860574 {A : Type'} (u : type686 A) : (term479 A u) = (term480 A u).
Proof. exact (MK_COMB (@lem4860573 A) (@lem4860572 A u)). Qed.
Lemma lem4860575 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4860576 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term471 A u) = s) = ((term478 A u) = s).
Proof. exact (MK_COMB (@lem4860574 A u) (@lem4860575 A s)). Qed.
Lemma lem4860577 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term478 A u) = s) = ((term471 A u) = s).
Proof. exact (SYM (@lem4860576 A u s)). Qed.
Lemma lem4860581 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term8 _111541 _111543 _111544 g s f) = (term9 _111541 _111543 _111544 f g s).
Proof. exact (EQ_MP (@lem4858548 _111541 _111543 _111544 f g s) (@lem4860096 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4860582 {A : Type'} (f : type672 A) (g : type672 A) (s : type686 A) : (term481 A g s f) = (term482 A f g s).
Proof. exact (@lem4860581 (A -> Prop) (A -> Prop) (A -> Prop) f g s). Qed.
Lemma lem4860583 {A : Type'} (u : type686 A) : (term483 A u) = (term484 A u).
Proof. exact (@lem4860582 A (term405 A) (term405 A) u). Qed.
Lemma lem4860584 {A : Type'} (t : A -> Prop) : (term436 A t) = (@DIFF A (@UNIV A) t).
Proof. exact (eq_refl (term436 A t)). Qed.
Lemma lem4860585 {A : Type'} (GEN_PVAR_65 : A -> Prop) (t : A -> Prop) (u : type686 A) : (term485 A GEN_PVAR_65 t u) = (term485 A GEN_PVAR_65 t u).
Proof. exact (eq_refl (term485 A GEN_PVAR_65 t u)). Qed.
Lemma lem4860586 {A : Type'} (GEN_PVAR_65 : A -> Prop) (u : type686 A) (t : A -> Prop) : (term486 A GEN_PVAR_65 u t) = (term487 A GEN_PVAR_65 u t).
Proof. exact (MK_COMB (@lem4860585 A GEN_PVAR_65 t u) (@lem4860584 A t)). Qed.
Lemma lem4860587 {A : Type'} (GEN_PVAR_65 : A -> Prop) (u : type686 A) : (term488 A GEN_PVAR_65 u) = (term489 A GEN_PVAR_65 u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4860586 A GEN_PVAR_65 u t)). Qed.
Lemma lem4860588 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4860589 {A : Type'} (GEN_PVAR_65 : A -> Prop) (u : type686 A) : (term490 A GEN_PVAR_65 u) = (term491 A GEN_PVAR_65 u).
Proof. exact (MK_COMB (@lem4860588 A) (@lem4860587 A GEN_PVAR_65 u)). Qed.
Lemma lem4860590 {A : Type'} (u : type686 A) : (term492 A u) = (term493 A u).
Proof. exact (fun_ext (fun GEN_PVAR_65 : A -> Prop => @lem4860589 A GEN_PVAR_65 u)). Qed.
Lemma lem4860591 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4860592 {A : Type'} (u : type686 A) : (term483 A u) = (term494 A u).
Proof. exact (MK_COMB (@lem4860591 A) (@lem4860590 A u)). Qed.
Lemma lem4860593 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4860594 {A : Type'} (u : type686 A) : (term495 A u) = (term496 A u).
Proof. exact (MK_COMB (@lem4860593 A) (@lem4860592 A u)). Qed.
Lemma lem4860595 {A : Type'} (x : A -> Prop) : (term497 A x) = (term433 A x).
Proof. exact (eq_refl (term497 A x)). Qed.
Lemma lem4860596 {A : Type'} : (term498 A) = (term499 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860595 A x)). Qed.
Lemma lem4860597 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4860598 {A : Type'} : (term500 A) = (term501 A).
Proof. exact (MK_COMB (@lem4860597 A) (@lem4860596 A)). Qed.
Lemma lem4860599 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860600 {A : Type'} (u : type686 A) : (term484 A u) = (term502 A u).
Proof. exact (MK_COMB (@lem4860598 A) (@lem4860599 A u)). Qed.
Lemma lem4860601 {A : Type'} (u : type686 A) : ((term483 A u) = (term484 A u)) = ((term494 A u) = (term502 A u)).
Proof. exact (MK_COMB (@lem4860594 A u) (@lem4860600 A u)). Qed.
Lemma lem4860602 {A : Type'} (u : type686 A) : (term494 A u) = (term502 A u).
Proof. exact (EQ_MP (@lem4860601 A u) (@lem4860583 A u)). Qed.
Lemma lem4860604 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860605 {A : Type'} (f : type672 A) (y : A -> Prop) : (term434 A f y) = (f y).
Proof. exact (@lem4860604 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4860606 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (@lem4860605 A (term405 A) x). Qed.
Lemma lem4860607 {A : Type'} (c : A -> Prop) : (term436 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term436 A c)). Qed.
Lemma lem4860608 {A : Type'} : (term437 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4860607 A c)). Qed.
Lemma lem4860609 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4860610 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (MK_COMB (@lem4860608 A) (@lem4860609 A x)). Qed.
Lemma lem4860611 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860612 {A : Type'} (x : A -> Prop) : (term438 A x) = (term439 A x).
Proof. exact (MK_COMB (@lem4860611 A) (@lem4860610 A x)). Qed.
Lemma lem4860613 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term436 A x)). Qed.
Lemma lem4860614 {A : Type'} (x : A -> Prop) : ((term435 A x) = (term436 A x)) = ((term436 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4860612 A x) (@lem4860613 A x)). Qed.
Lemma lem4860615 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4860614 A x) (@lem4860606 A x)). Qed.
Lemma lem4860616 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860617 {A : Type'} (x : A -> Prop) : (term433 A x) = (term389 A x).
Proof. exact (MK_COMB (@lem4860616 A) (@lem4860615 A x)). Qed.
Lemma lem4860618 {A : Type'} : (term499 A) = (term503 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860617 A x)). Qed.
Lemma lem4860619 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4860620 {A : Type'} : (term501 A) = (term504 A).
Proof. exact (MK_COMB (@lem4860619 A) (@lem4860618 A)). Qed.
Lemma lem4860621 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860622 {A : Type'} (u : type686 A) : (term502 A u) = (term505 A u).
Proof. exact (MK_COMB (@lem4860620 A) (@lem4860621 A u)). Qed.
Lemma lem4860623 {A : Type'} (u : type686 A) : (term494 A u) = (term505 A u).
Proof. exact (TRANS (@lem4860602 A u) (@lem4860622 A u)). Qed.
Lemma lem4860624 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4860625 {A : Type'} (u : type686 A) : (term506 A u) = (term507 A u).
Proof. exact (MK_COMB (@lem4860624 A) (@lem4860623 A u)). Qed.
Lemma lem4860626 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860627 {A : Type'} (u : type686 A) : (term475 A u) = (term508 A u).
Proof. exact (MK_COMB (@lem4860626 A) (@lem4860625 A u)). Qed.
Lemma lem4860628 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860629 {A : Type'} (u : type686 A) : (term477 A u) = (term509 A u).
Proof. exact (MK_COMB (@lem4860628 A) (@lem4860627 A u)). Qed.
Lemma lem4860630 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860631 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term475 A u) = (@DIFF A (@UNIV A) s)) = ((term508 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (MK_COMB (@lem4860629 A u) (@lem4860630 A s)). Qed.
Lemma lem4860634 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term508 A u) = (@DIFF A (@UNIV A) s)) = ((term475 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (SYM (@lem4860631 A u s)). Qed.
Lemma lem4860638 {_111541 _111543 _111544 : Type'} (f : _111543 -> _111541) (g : _111544 -> _111543) (s : _111544 -> Prop) : (term8 _111541 _111543 _111544 g s f) = (term9 _111541 _111543 _111544 f g s).
Proof. exact (EQ_MP (@lem4858548 _111541 _111543 _111544 f g s) (@lem4860096 _111541 _111543 _111544 f g s)). Qed.
Lemma lem4860639 {A : Type'} (f : type672 A) (g : type672 A) (s : type686 A) : (term481 A g s f) = (term482 A f g s).
Proof. exact (@lem4860638 (A -> Prop) (A -> Prop) (A -> Prop) f g s). Qed.
Lemma lem4860640 {A : Type'} (u : type686 A) : (term483 A u) = (term484 A u).
Proof. exact (@lem4860639 A (term405 A) (term405 A) u). Qed.
Lemma lem4860641 {A : Type'} (t : A -> Prop) : (term436 A t) = (@DIFF A (@UNIV A) t).
Proof. exact (eq_refl (term436 A t)). Qed.
Lemma lem4860642 {A : Type'} (GEN_PVAR_66 : A -> Prop) (t : A -> Prop) (u : type686 A) : (term485 A GEN_PVAR_66 t u) = (term485 A GEN_PVAR_66 t u).
Proof. exact (eq_refl (term485 A GEN_PVAR_66 t u)). Qed.
Lemma lem4860643 {A : Type'} (GEN_PVAR_66 : A -> Prop) (u : type686 A) (t : A -> Prop) : (term486 A GEN_PVAR_66 u t) = (term487 A GEN_PVAR_66 u t).
Proof. exact (MK_COMB (@lem4860642 A GEN_PVAR_66 t u) (@lem4860641 A t)). Qed.
Lemma lem4860644 {A : Type'} (GEN_PVAR_66 : A -> Prop) (u : type686 A) : (term488 A GEN_PVAR_66 u) = (term489 A GEN_PVAR_66 u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4860643 A GEN_PVAR_66 u t)). Qed.
Lemma lem4860645 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4860646 {A : Type'} (GEN_PVAR_66 : A -> Prop) (u : type686 A) : (term490 A GEN_PVAR_66 u) = (term491 A GEN_PVAR_66 u).
Proof. exact (MK_COMB (@lem4860645 A) (@lem4860644 A GEN_PVAR_66 u)). Qed.
Lemma lem4860647 {A : Type'} (u : type686 A) : (term492 A u) = (term493 A u).
Proof. exact (fun_ext (fun GEN_PVAR_66 : A -> Prop => @lem4860646 A GEN_PVAR_66 u)). Qed.
Lemma lem4860648 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4860649 {A : Type'} (u : type686 A) : (term483 A u) = (term494 A u).
Proof. exact (MK_COMB (@lem4860648 A) (@lem4860647 A u)). Qed.
Lemma lem4860650 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4860651 {A : Type'} (u : type686 A) : (term495 A u) = (term496 A u).
Proof. exact (MK_COMB (@lem4860650 A) (@lem4860649 A u)). Qed.
Lemma lem4860652 {A : Type'} (x : A -> Prop) : (term497 A x) = (term433 A x).
Proof. exact (eq_refl (term497 A x)). Qed.
Lemma lem4860653 {A : Type'} : (term498 A) = (term499 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860652 A x)). Qed.
Lemma lem4860654 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4860655 {A : Type'} : (term500 A) = (term501 A).
Proof. exact (MK_COMB (@lem4860654 A) (@lem4860653 A)). Qed.
Lemma lem4860656 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860657 {A : Type'} (u : type686 A) : (term484 A u) = (term502 A u).
Proof. exact (MK_COMB (@lem4860655 A) (@lem4860656 A u)). Qed.
Lemma lem4860658 {A : Type'} (u : type686 A) : ((term483 A u) = (term484 A u)) = ((term494 A u) = (term502 A u)).
Proof. exact (MK_COMB (@lem4860651 A u) (@lem4860657 A u)). Qed.
Lemma lem4860659 {A : Type'} (u : type686 A) : (term494 A u) = (term502 A u).
Proof. exact (EQ_MP (@lem4860658 A u) (@lem4860640 A u)). Qed.
Lemma lem4860661 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860662 {A : Type'} (f : type672 A) (y : A -> Prop) : (term434 A f y) = (f y).
Proof. exact (@lem4860661 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4860663 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (@lem4860662 A (term405 A) x). Qed.
Lemma lem4860664 {A : Type'} (c : A -> Prop) : (term436 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term436 A c)). Qed.
Lemma lem4860665 {A : Type'} : (term437 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4860664 A c)). Qed.
Lemma lem4860666 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4860667 {A : Type'} (x : A -> Prop) : (term435 A x) = (term436 A x).
Proof. exact (MK_COMB (@lem4860665 A) (@lem4860666 A x)). Qed.
Lemma lem4860668 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860669 {A : Type'} (x : A -> Prop) : (term438 A x) = (term439 A x).
Proof. exact (MK_COMB (@lem4860668 A) (@lem4860667 A x)). Qed.
Lemma lem4860670 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term436 A x)). Qed.
Lemma lem4860671 {A : Type'} (x : A -> Prop) : ((term435 A x) = (term436 A x)) = ((term436 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4860669 A x) (@lem4860670 A x)). Qed.
Lemma lem4860672 {A : Type'} (x : A -> Prop) : (term436 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4860671 A x) (@lem4860663 A x)). Qed.
Lemma lem4860673 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860674 {A : Type'} (x : A -> Prop) : (term433 A x) = (term389 A x).
Proof. exact (MK_COMB (@lem4860673 A) (@lem4860672 A x)). Qed.
Lemma lem4860675 {A : Type'} : (term499 A) = (term503 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860674 A x)). Qed.
Lemma lem4860676 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4860677 {A : Type'} : (term501 A) = (term504 A).
Proof. exact (MK_COMB (@lem4860676 A) (@lem4860675 A)). Qed.
Lemma lem4860678 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860679 {A : Type'} (u : type686 A) : (term502 A u) = (term505 A u).
Proof. exact (MK_COMB (@lem4860677 A) (@lem4860678 A u)). Qed.
Lemma lem4860680 {A : Type'} (u : type686 A) : (term494 A u) = (term505 A u).
Proof. exact (TRANS (@lem4860659 A u) (@lem4860679 A u)). Qed.
Lemma lem4860681 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem4860682 {A : Type'} (u : type686 A) : (term510 A u) = (term511 A u).
Proof. exact (MK_COMB (@lem4860681 A) (@lem4860680 A u)). Qed.
Lemma lem4860683 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860684 {A : Type'} (u : type686 A) : (term478 A u) = (term512 A u).
Proof. exact (MK_COMB (@lem4860683 A) (@lem4860682 A u)). Qed.
Lemma lem4860685 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860686 {A : Type'} (u : type686 A) : (term480 A u) = (term513 A u).
Proof. exact (MK_COMB (@lem4860685 A) (@lem4860684 A u)). Qed.
Lemma lem4860687 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4860688 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term478 A u) = s) = ((term512 A u) = s).
Proof. exact (MK_COMB (@lem4860686 A u) (@lem4860687 A s)). Qed.
Lemma lem4860691 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term512 A u) = s) = ((term478 A u) = s).
Proof. exact (SYM (@lem4860688 A u s)). Qed.
Lemma lem4860692 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4860693 {A : Type'} (s : A -> Prop) : (term388 A s) = ((term389 A s) = s).
Proof. exact (eq_refl (term388 A s)). Qed.
Lemma lem4860695 {_87528 : Type'} (s : _87528 -> Prop) : term514 _87528 s.
Proof. exact (@lem3368911 _87528 s). Qed.
Lemma lem4860696 {_87528 : Type'} (s : _87528 -> Prop) : (term514 _87528 s) = ((term515 _87528 s) = s).
Proof. exact (eq_refl (term514 _87528 s)). Qed.
Lemma lem4860710 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4860693 A s) (@lem4860692 A s)). Qed.
Lemma lem4860711 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4860710 A s). Qed.
Lemma lem4860712 {A : Type'} (x : A -> Prop) : (term389 A x) = x.
Proof. exact (@lem4860711 A x). Qed.
Lemma lem4860713 {A : Type'} : (term503 A) = (term516 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860712 A x)). Qed.
Lemma lem4860714 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4860715 {A : Type'} : (term504 A) = (term517 A).
Proof. exact (MK_COMB (@lem4860714 A) (@lem4860713 A)). Qed.
Lemma lem4860716 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860717 {A : Type'} (u : type686 A) : (term505 A u) = (term518 A u).
Proof. exact (MK_COMB (@lem4860715 A) (@lem4860716 A u)). Qed.
Lemma lem4860719 {_87528 : Type'} (s : _87528 -> Prop) : (term515 _87528 s) = s.
Proof. exact (EQ_MP (@lem4860696 _87528 s) (@lem4860695 _87528 s)). Qed.
Lemma lem4860720 {A : Type'} (s : type686 A) : (term518 A s) = s.
Proof. exact (@lem4860719 (A -> Prop) s). Qed.
Lemma lem4860721 {A : Type'} (u : type686 A) : (term518 A u) = u.
Proof. exact (@lem4860720 A u). Qed.
Lemma lem4860722 {A : Type'} (u : type686 A) : (term505 A u) = u.
Proof. exact (TRANS (@lem4860717 A u) (@lem4860721 A u)). Qed.
Lemma lem4860723 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4860724 {A : Type'} (u : type686 A) : (term507 A u) = (@UNIONS A u).
Proof. exact (MK_COMB (@lem4860723 A) (@lem4860722 A u)). Qed.
Lemma lem4860726 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4860727 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term507 A u) = s.
Proof. exact (TRANS (@lem4860724 A u) (@lem4860726 A u s h1)). Qed.
Lemma lem4860728 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860729 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term508 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (MK_COMB (@lem4860728 A) (@lem4860727 A u s h1)). Qed.
Lemma lem4860730 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860731 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term509 A u) = (term519 A s).
Proof. exact (MK_COMB (@lem4860730 A) (@lem4860729 A u s h1)). Qed.
Lemma lem4860732 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860733 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : ((term508 A u) = (@DIFF A (@UNIV A) s)) = ((@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s)).
Proof. exact (MK_COMB (@lem4860731 A u s h1) (@lem4860732 A s)). Qed.
Lemma lem4860735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4860736 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4860735 (A -> Prop) x). Qed.
Lemma lem4860737 {A : Type'} (s : A -> Prop) : ((@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s)) = True.
Proof. exact (@lem4860736 A (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860738 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : ((term508 A u) = (@DIFF A (@UNIV A) s)) = True.
Proof. exact (TRANS (@lem4860733 A u s h1) (@lem4860737 A s)). Qed.
Lemma lem4860739 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : True = ((term508 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (SYM (@lem4860738 A u s h1)). Qed.
Lemma lem4860740 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term508 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (EQ_MP (@lem4860739 A u s h1) (@lem0)). Qed.
Lemma lem4860741 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4860742 {A : Type'} (s : A -> Prop) : (term388 A s) = ((term389 A s) = s).
Proof. exact (eq_refl (term388 A s)). Qed.
Lemma lem4860744 {_87528 : Type'} (s : _87528 -> Prop) : term514 _87528 s.
Proof. exact (@lem3368911 _87528 s). Qed.
Lemma lem4860745 {_87528 : Type'} (s : _87528 -> Prop) : (term514 _87528 s) = ((term515 _87528 s) = s).
Proof. exact (eq_refl (term514 _87528 s)). Qed.
Lemma lem4860759 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4860742 A s) (@lem4860741 A s)). Qed.
Lemma lem4860760 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4860759 A s). Qed.
Lemma lem4860761 {A : Type'} (x : A -> Prop) : (term389 A x) = x.
Proof. exact (@lem4860760 A x). Qed.
Lemma lem4860762 {A : Type'} : (term503 A) = (term516 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4860761 A x)). Qed.
Lemma lem4860763 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4860764 {A : Type'} : (term504 A) = (term517 A).
Proof. exact (MK_COMB (@lem4860763 A) (@lem4860762 A)). Qed.
Lemma lem4860765 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4860766 {A : Type'} (u : type686 A) : (term505 A u) = (term518 A u).
Proof. exact (MK_COMB (@lem4860764 A) (@lem4860765 A u)). Qed.
Lemma lem4860768 {_87528 : Type'} (s : _87528 -> Prop) : (term515 _87528 s) = s.
Proof. exact (EQ_MP (@lem4860745 _87528 s) (@lem4860744 _87528 s)). Qed.
Lemma lem4860769 {A : Type'} (s : type686 A) : (term518 A s) = s.
Proof. exact (@lem4860768 (A -> Prop) s). Qed.
Lemma lem4860770 {A : Type'} (u : type686 A) : (term518 A u) = u.
Proof. exact (@lem4860769 A u). Qed.
Lemma lem4860771 {A : Type'} (u : type686 A) : (term505 A u) = u.
Proof. exact (TRANS (@lem4860766 A u) (@lem4860770 A u)). Qed.
Lemma lem4860772 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem4860773 {A : Type'} (u : type686 A) : (term511 A u) = (@INTERS A u).
Proof. exact (MK_COMB (@lem4860772 A) (@lem4860771 A u)). Qed.
Lemma lem4860775 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (@INTERS A u) = (@DIFF A (@UNIV A) s).
Proof. exact (h1). Qed.
Lemma lem4860776 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term511 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (TRANS (@lem4860773 A u) (@lem4860775 A u s h1)). Qed.
Lemma lem4860777 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4860778 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term512 A u) = (term389 A s).
Proof. exact (MK_COMB (@lem4860777 A) (@lem4860776 A u s h1)). Qed.
Lemma lem4860780 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4860742 A s) (@lem4860741 A s)). Qed.
Lemma lem4860781 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4860780 A s). Qed.
Lemma lem4860782 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term512 A u) = s.
Proof. exact (TRANS (@lem4860778 A u s h1) (@lem4860781 A s)). Qed.
Lemma lem4860783 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4860784 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term513 A u) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem4860783 A) (@lem4860782 A u s h1)). Qed.
Lemma lem4860785 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4860786 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : ((term512 A u) = s) = (s = s).
Proof. exact (MK_COMB (@lem4860784 A u s h1) (@lem4860785 A s)). Qed.
Lemma lem4860788 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4860789 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4860788 (A -> Prop) x). Qed.
Lemma lem4860790 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem4860789 A s). Qed.
Lemma lem4860791 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : ((term512 A u) = s) = True.
Proof. exact (TRANS (@lem4860786 A u s h1) (@lem4860790 A s)). Qed.
Lemma lem4860792 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : True = ((term512 A u) = s).
Proof. exact (SYM (@lem4860791 A u s h1)). Qed.
Lemma lem4860793 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term512 A u) = s.
Proof. exact (EQ_MP (@lem4860792 A u s h1) (@lem0)). Qed.
Lemma lem4860794 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term478 A u) = s.
Proof. exact (EQ_MP (@lem4860691 A u s) (@lem4860793 A u s h1)). Qed.
Lemma lem4860795 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term475 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (EQ_MP (@lem4860634 A u s) (@lem4860740 A u s h1)). Qed.
Lemma lem4860796 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term471 A u) = s.
Proof. exact (EQ_MP (@lem4860577 A u s) (@lem4860794 A u s h1)). Qed.
Lemma lem4860797 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term450 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (EQ_MP (@lem4860566 A u s) (@lem4860795 A u s h1)). Qed.
Lemma lem4860798 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term474 A P u s.
Proof. exact (EQ_MP (@lem4860555 A s u P h1) (@lem4860796 A u s h2)). Qed.
Lemma lem4860799 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : (@UNIONS A u) = s) : term453 A P u s.
Proof. exact (EQ_MP (@lem4860431 A s u P h1) (@lem4860797 A u s h2)). Qed.
Lemma lem4860800 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term341 A P s.
Proof. exact (ex_intro (term520 A P s) (term399 A u) (@lem4860798 A P u s h1 h2)). Qed.
Lemma lem4860801 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : (@UNIONS A u) = s) : term382 A P s.
Proof. exact (ex_intro (term521 A P s) (term399 A u) (@lem4860799 A P u s h1 h2)). Qed.
Lemma lem4860802 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : term387 A P u s.
Proof. exact (proj2 (@lem4860278 A P u s h1)). Qed.
Lemma lem4860804 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : (@INTERS A u) = (@DIFF A (@UNIV A) s).
Proof. exact (proj2 (@lem4860279 A P u s h1)). Qed.
Lemma lem4860805 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : term362 A u P.
Proof. exact (proj1 (@lem4860279 A P u s h1)). Qed.
Lemma lem4860806 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : ((@INTERS A u) = (@DIFF A (@UNIV A) s)) = (term341 A P s).
Proof. exact (prop_ext (fun h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s) => @lem4860800 A P u s h1 h2) (fun h3 : term341 A P s => @lem4860281 A u s h2)). Qed.
Lemma lem4860807 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term341 A P s.
Proof. exact (EQ_MP (@lem4860806 A P u s h1 h2) (@lem4860281 A u s h2)). Qed.
Lemma lem4860808 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term362 A u P) = (term341 A P s).
Proof. exact (prop_ext (fun h3 : term362 A u P => @lem4860807 A P u s h1 h2) (fun h3 : term341 A P s => @lem4860282 A u P h1)). Qed.
Lemma lem4860809 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term341 A P s.
Proof. exact (EQ_MP (@lem4860808 A P u s h1 h2) (@lem4860282 A u P h1)). Qed.
Lemma lem4860810 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : term387 A P u s) : ((@INTERS A u) = (@DIFF A (@UNIV A) s)) = (term341 A P s).
Proof. exact (prop_ext (fun h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s) => @lem4860809 A P u s h1 h3) (fun h3 : term341 A P s => @lem4860804 A P u s h2)). Qed.
Lemma lem4860811 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : term387 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4860810 A P u s h1 h2) (@lem4860804 A P u s h2)). Qed.
Lemma lem4860812 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : (term362 A u P) = (term341 A P s).
Proof. exact (prop_ext (fun h2 : term362 A u P => @lem4860811 A P u s h2 h1) (fun h2 : term341 A P s => @lem4860805 A P u s h1)). Qed.
Lemma lem4860813 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4860812 A P u s h1) (@lem4860805 A P u s h1)). Qed.
Lemma lem4860814 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : (term387 A P u s) = (term341 A P s).
Proof. exact (prop_ext (fun h2 : term387 A P u s => @lem4860813 A P u s h2) (fun h2 : term341 A P s => @lem4860802 A P u s h1)). Qed.
Lemma lem4860815 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4860814 A P u s h1) (@lem4860802 A P u s h1)). Qed.
Lemma lem4860816 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term382 A P s) : term341 A P s.
Proof. exact (ex_elim (@lem4860277 A P s h1) (fun u : type686 A => fun h0 : term521 A P s u => @lem4860815 A P u s h0)). Qed.
Lemma lem4860817 {A : Type'} (P : type686 A) (s : A -> Prop) : term522 A P s.
Proof. exact (fun h0 : term382 A P s => @lem4860816 A P s h0). Qed.
Lemma lem4860818 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : term384 A P u s.
Proof. exact (proj2 (@lem4860272 A P u s h1)). Qed.
Lemma lem4860820 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : (@UNIONS A u) = s.
Proof. exact (proj2 (@lem4860273 A P u s h1)). Qed.
Lemma lem4860821 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : term385 A u P.
Proof. exact (proj1 (@lem4860273 A P u s h1)). Qed.
Lemma lem4860822 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : (@UNIONS A u) = s) : ((@UNIONS A u) = s) = (term382 A P s).
Proof. exact (prop_ext (fun h3 : (@UNIONS A u) = s => @lem4860801 A P u s h1 h2) (fun h3 : term382 A P s => @lem4860275 A u s h2)). Qed.
Lemma lem4860823 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : (@UNIONS A u) = s) : term382 A P s.
Proof. exact (EQ_MP (@lem4860822 A P u s h1 h2) (@lem4860275 A u s h2)). Qed.
Lemma lem4860824 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : (@UNIONS A u) = s) : (term385 A u P) = (term382 A P s).
Proof. exact (prop_ext (fun h3 : term385 A u P => @lem4860823 A P u s h1 h2) (fun h3 : term382 A P s => @lem4860276 A u P h1)). Qed.
Lemma lem4860825 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : (@UNIONS A u) = s) : term382 A P s.
Proof. exact (EQ_MP (@lem4860824 A P u s h1 h2) (@lem4860276 A u P h1)). Qed.
Lemma lem4860826 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : term384 A P u s) : ((@UNIONS A u) = s) = (term382 A P s).
Proof. exact (prop_ext (fun h3 : (@UNIONS A u) = s => @lem4860825 A P u s h1 h3) (fun h3 : term382 A P s => @lem4860820 A P u s h2)). Qed.
Lemma lem4860827 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : term384 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4860826 A P u s h1 h2) (@lem4860820 A P u s h2)). Qed.
Lemma lem4860828 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : (term385 A u P) = (term382 A P s).
Proof. exact (prop_ext (fun h2 : term385 A u P => @lem4860827 A P u s h2 h1) (fun h2 : term382 A P s => @lem4860821 A P u s h1)). Qed.
Lemma lem4860829 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4860828 A P u s h1) (@lem4860821 A P u s h1)). Qed.
Lemma lem4860830 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : (term384 A P u s) = (term382 A P s).
Proof. exact (prop_ext (fun h2 : term384 A P u s => @lem4860829 A P u s h2) (fun h2 : term382 A P s => @lem4860818 A P u s h1)). Qed.
Lemma lem4860831 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4860830 A P u s h1) (@lem4860818 A P u s h1)). Qed.
Lemma lem4860832 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term341 A P s) : term382 A P s.
Proof. exact (ex_elim (@lem4860271 A P s h1) (fun u : type686 A => fun h0 : term520 A P s u => @lem4860831 A P u s h0)). Qed.
Lemma lem4860833 {A : Type'} (P : type686 A) (s : A -> Prop) : term523 A P s.
Proof. exact (fun h0 : term341 A P s => @lem4860832 A P s h0). Qed.
Lemma lem4860834 {A : Type'} (P : type686 A) (s : A -> Prop) : term524 A P s.
Proof. exact (conj (@lem4860833 A P s) (@lem4860817 A P s)). Qed.
Lemma lem4860835 {A : Type'} (P : type686 A) (s : A -> Prop) : (term524 A P s) = ((term341 A P s) = (term382 A P s)).
Proof. exact (@lem32 (term341 A P s) (term382 A P s)). Qed.
Lemma lem4860836 {A : Type'} (P : type686 A) (s : A -> Prop) : (term341 A P s) = (term382 A P s).
Proof. exact (EQ_MP (@lem4860835 A P s) (@lem4860834 A P s)). Qed.
Lemma lem4860837 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term375 A P s).
Proof. exact (EQ_MP (@lem4860270 A P s) (@lem4860836 A P s)). Qed.
Lemma lem4860842 {A : Type'} (P : type686 A) : term525 A P.
Proof. exact (fun s : A -> Prop => @lem4860837 A P s). Qed.
Lemma lem4860847 {A : Type'} : term526 A.
Proof. exact (fun P : type686 A => @lem4860842 A P). Qed.
