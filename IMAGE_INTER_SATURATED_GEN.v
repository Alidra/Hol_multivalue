Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTER_SATURATED_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3488495 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3488496 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3488497 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3488496 t1) (@lem3488495 t1)). Qed.
Lemma lem3488498 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3488497 t1 t2). Qed.
Lemma lem3488499 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3488500 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3488499 t1 t2) (@lem3488498 t1 t2)). Qed.
Lemma lem3488501 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3488500 t1 t2 t3). Qed.
Lemma lem3488502 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3488503 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3488502 t1 t2 t3) (@lem3488501 t1 t2 t3)). Qed.
Lemma lem3488504 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3488503 t1 t2 t3)). Qed.
Lemma lem3488528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3488529 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3488528 A s t). Qed.
Lemma lem3488530 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term8 A B u f s) = (term9 A B u f s).
Proof. exact (@lem3488529 A (term10 A B u f s) s). Qed.
Lemma lem3488543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488544 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term11 A B u f s) = (term12 A B u f s).
Proof. exact (MK_COMB (@lem3488543) (@lem3488530 A B u f s)). Qed.
Lemma lem3488546 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3488547 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3488546 A s t). Qed.
Lemma lem3488548 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term7 A t u).
Proof. exact (@lem3488547 A t u). Qed.
Lemma lem3488555 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term13 A B f s t u) = (term14 A B f s t u).
Proof. exact (MK_COMB (@lem3488544 A B u f s) (@lem3488548 A t u)). Qed.
Lemma lem3488558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3488559 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term15 A B f s t u) = (term16 A B f s t u).
Proof. exact (MK_COMB (@lem3488558) (@lem3488555 A B f s t u)). Qed.
Lemma lem3488563 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3488564 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3488563 A s t). Qed.
Lemma lem3488565 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term8 A B u f t) = (term9 A B u f t).
Proof. exact (@lem3488564 A (term10 A B u f t) t). Qed.
Lemma lem3488578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488579 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term11 A B u f t) = (term12 A B u f t).
Proof. exact (MK_COMB (@lem3488578) (@lem3488565 A B u f t)). Qed.
Lemma lem3488581 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3488582 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3488581 A s t). Qed.
Lemma lem3488583 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term7 A s u).
Proof. exact (@lem3488582 A s u). Qed.
Lemma lem3488590 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term13 A B f t s u) = (term14 A B f t s u).
Proof. exact (MK_COMB (@lem3488579 A B u f t) (@lem3488583 A s u)). Qed.
Lemma lem3488593 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term17 A B f t s u) = (term18 A B f t s u).
Proof. exact (MK_COMB (@lem3488559 A B f s t u) (@lem3488590 A B f t s u)). Qed.
Lemma lem3488596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3488597 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term19 A B f t s u) = (term20 A B f t s u).
Proof. exact (MK_COMB (@lem3488596) (@lem3488593 A B f t s u)). Qed.
Lemma lem3488601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3488602 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term21 B s t).
Proof. exact (@lem3488601 B s t). Qed.
Lemma lem3488603 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term22 A B f s t) = (term23 A B s f t)) = (term24 A B s f t).
Proof. exact (@lem3488602 B (term22 A B f s t) (term23 A B s f t)). Qed.
Lemma lem3488612 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term25 A B u s f t) = (term26 A B u s f t).
Proof. exact (MK_COMB (@lem3488597 A B f t s u) (@lem3488603 A B s f t)). Qed.
Lemma lem3488615 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term27 A B s f t) = (term28 A B s f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3488612 A B u s f t)). Qed.
Lemma lem3488616 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3488617 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term29 A B s f t) = (term30 A B s f t).
Proof. exact (MK_COMB (@lem3488616 A) (@lem3488615 A B s f t)). Qed.
Lemma lem3488622 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term31 A B s f) = (term32 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3488617 A B s f t)). Qed.
Lemma lem3488623 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3488624 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term33 A B s f) = (term34 A B s f).
Proof. exact (MK_COMB (@lem3488623 A) (@lem3488622 A B s f)). Qed.
Lemma lem3488629 {A B : Type'} (f : A -> B) : (term35 A B f) = (term36 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3488624 A B s f)). Qed.
Lemma lem3488630 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3488631 {A B : Type'} (f : A -> B) : (term37 A B f) = (term38 A B f).
Proof. exact (MK_COMB (@lem3488630 A) (@lem3488629 A B f)). Qed.
Lemma lem3488636 {A B : Type'} : (term39 A B) = (term40 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3488631 A B f)). Qed.
Lemma lem3488637 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3488638 {A B : Type'} : (term41 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem3488637 A B) (@lem3488636 A B)). Qed.
Lemma lem3488643 {A B : Type'} : (term42 A B) = (term41 A B).
Proof. exact (SYM (@lem3488638 A B)). Qed.
Lemma lem3488673 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term43 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3488674 {A : Type'} (p : A -> Prop) (x : A) : (term43 A x p) = (p x).
Proof. exact (@lem3488673 A p x). Qed.
Lemma lem3488675 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term44 A B x u f s) = (term45 A B u f s x).
Proof. exact (@lem3488674 A (term46 A B u f s) x). Qed.
Lemma lem3488676 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term45 A B u f s x) = (term47 A B u x f s).
Proof. exact (eq_refl (term45 A B u f s x)). Qed.
Lemma lem3488677 {A : Type'} (GEN_PVAR_82 : A) : (@SETSPEC A GEN_PVAR_82) = (@SETSPEC A GEN_PVAR_82).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_82)). Qed.
Lemma lem3488678 {A B : Type'} (GEN_PVAR_82 : A) (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term48 A B GEN_PVAR_82 u f s x) = (term49 A B GEN_PVAR_82 u x f s).
Proof. exact (MK_COMB (@lem3488677 A GEN_PVAR_82) (@lem3488676 A B u x f s)). Qed.
Lemma lem3488679 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3488680 {A B : Type'} (GEN_PVAR_82 : A) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term50 A B GEN_PVAR_82 u f s x) = (term51 A B GEN_PVAR_82 u f s x).
Proof. exact (MK_COMB (@lem3488678 A B GEN_PVAR_82 u x f s) (@lem3488679 A x)). Qed.
Lemma lem3488681 {A B : Type'} (GEN_PVAR_82 : A) (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term52 A B GEN_PVAR_82 u f s) = (term53 A B GEN_PVAR_82 u f s).
Proof. exact (fun_ext (fun x : A => @lem3488680 A B GEN_PVAR_82 u f s x)). Qed.
Lemma lem3488682 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3488683 {A B : Type'} (GEN_PVAR_82 : A) (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term54 A B GEN_PVAR_82 u f s) = (term55 A B GEN_PVAR_82 u f s).
Proof. exact (MK_COMB (@lem3488682 A) (@lem3488681 A B GEN_PVAR_82 u f s)). Qed.
Lemma lem3488684 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term56 A B u f s) = (term57 A B u f s).
Proof. exact (fun_ext (fun GEN_PVAR_82 : A => @lem3488683 A B GEN_PVAR_82 u f s)). Qed.
Lemma lem3488685 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3488686 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term58 A B u f s) = (term10 A B u f s).
Proof. exact (MK_COMB (@lem3488685 A) (@lem3488684 A B u f s)). Qed.
Lemma lem3488687 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3488688 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term44 A B x u f s) = (term59 A B x u f s).
Proof. exact (MK_COMB (@lem3488687 A x) (@lem3488686 A B u f s)). Qed.
Lemma lem3488689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3488690 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term60 A B x u f s) = (term61 A B x u f s).
Proof. exact (MK_COMB (@lem3488689) (@lem3488688 A B x u f s)). Qed.
Lemma lem3488691 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term45 A B u f s x) = (term47 A B u x f s).
Proof. exact (eq_refl (term45 A B u f s x)). Qed.
Lemma lem3488692 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : ((term44 A B x u f s) = (term45 A B u f s x)) = ((term59 A B x u f s) = (term47 A B u x f s)).
Proof. exact (MK_COMB (@lem3488690 A B x u f s) (@lem3488691 A B u x f s)). Qed.
Lemma lem3488693 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term59 A B x u f s) = (term47 A B u x f s).
Proof. exact (EQ_MP (@lem3488692 A B u x f s) (@lem3488675 A B u f s x)). Qed.
Lemma lem3488697 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488698 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488697 A P x). Qed.
Lemma lem3488699 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3488698 A u x). Qed.
Lemma lem3488700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488701 {A : Type'} (u : A -> Prop) (x : A) : (term62 A x u) = (term63 A u x).
Proof. exact (MK_COMB (@lem3488700) (@lem3488699 A u x)). Qed.
Lemma lem3488703 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3488704 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (@lem3488703 A B y f s). Qed.
Lemma lem3488705 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term66 A B x f s) = (term67 A B x f s).
Proof. exact (@lem3488704 A B (f x) f s). Qed.
Lemma lem3488715 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488716 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488715 A P x). Qed.
Lemma lem3488717 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3488716 A s x'). Qed.
Lemma lem3488718 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term68 A B x f x') = (term68 A B x f x').
Proof. exact (eq_refl (term68 A B x f x')). Qed.
Lemma lem3488719 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term69 A B x f x' s) = (term70 A B x f s x').
Proof. exact (MK_COMB (@lem3488718 A B x f x') (@lem3488717 A s x')). Qed.
Lemma lem3488722 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term72 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3488719 A B x f s x')). Qed.
Lemma lem3488723 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3488724 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term67 A B x f s) = (term73 A B x f s).
Proof. exact (MK_COMB (@lem3488723 A) (@lem3488722 A B x f s)). Qed.
Lemma lem3488729 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term66 A B x f s) = (term73 A B x f s).
Proof. exact (TRANS (@lem3488705 A B x f s) (@lem3488724 A B x f s)). Qed.
Lemma lem3488730 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term47 A B u x f s) = (term74 A B u x f s).
Proof. exact (MK_COMB (@lem3488701 A u x) (@lem3488729 A B x f s)). Qed.
Lemma lem3488733 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term59 A B x u f s) = (term74 A B u x f s).
Proof. exact (TRANS (@lem3488693 A B u x f s) (@lem3488730 A B u x f s)). Qed.
Lemma lem3488734 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3488735 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term75 A B x u f s) = (term76 A B u x f s).
Proof. exact (MK_COMB (@lem3488734) (@lem3488733 A B u x f s)). Qed.
Lemma lem3488737 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488738 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488737 A P x). Qed.
Lemma lem3488739 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3488738 A s x). Qed.
Lemma lem3488740 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term77 A B u f x s) = (term78 A B u f s x).
Proof. exact (MK_COMB (@lem3488735 A B u x f s) (@lem3488739 A s x)). Qed.
Lemma lem3488743 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term79 A B u f s) = (term80 A B u f s).
Proof. exact (fun_ext (fun x : A => @lem3488740 A B u f s x)). Qed.
Lemma lem3488744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3488745 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term9 A B u f s) = (term81 A B u f s).
Proof. exact (MK_COMB (@lem3488744 A) (@lem3488743 A B u f s)). Qed.
Lemma lem3488750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488751 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term12 A B u f s) = (term82 A B u f s).
Proof. exact (MK_COMB (@lem3488750) (@lem3488745 A B u f s)). Qed.
Lemma lem3488759 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488759 A P x). Qed.
Lemma lem3488761 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3488760 A t x). Qed.
Lemma lem3488762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3488763 {A : Type'} (t : A -> Prop) (x : A) : (term83 A x t) = (term84 A t x).
Proof. exact (MK_COMB (@lem3488762) (@lem3488761 A t x)). Qed.
Lemma lem3488765 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488766 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488765 A P x). Qed.
Lemma lem3488767 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3488766 A u x). Qed.
Lemma lem3488768 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term85 A t x u) = (term86 A t u x).
Proof. exact (MK_COMB (@lem3488763 A t x) (@lem3488767 A u x)). Qed.
Lemma lem3488771 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term87 A t u) = (term88 A t u).
Proof. exact (fun_ext (fun x : A => @lem3488768 A t u x)). Qed.
Lemma lem3488772 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3488773 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term7 A t u) = (term89 A t u).
Proof. exact (MK_COMB (@lem3488772 A) (@lem3488771 A t u)). Qed.
Lemma lem3488778 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term14 A B f s t u) = (term90 A B f s t u).
Proof. exact (MK_COMB (@lem3488751 A B u f s) (@lem3488773 A t u)). Qed.
Lemma lem3488781 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3488782 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term16 A B f s t u) = (term91 A B f s t u).
Proof. exact (MK_COMB (@lem3488781) (@lem3488778 A B f s t u)). Qed.
Lemma lem3488792 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term43 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3488793 {A : Type'} (p : A -> Prop) (x : A) : (term43 A x p) = (p x).
Proof. exact (@lem3488792 A p x). Qed.
Lemma lem3488794 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term44 A B x u f t) = (term45 A B u f t x).
Proof. exact (@lem3488793 A (term46 A B u f t) x). Qed.
Lemma lem3488795 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term45 A B u f t x) = (term47 A B u x f t).
Proof. exact (eq_refl (term45 A B u f t x)). Qed.
Lemma lem3488796 {A : Type'} (GEN_PVAR_83 : A) : (@SETSPEC A GEN_PVAR_83) = (@SETSPEC A GEN_PVAR_83).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_83)). Qed.
Lemma lem3488797 {A B : Type'} (GEN_PVAR_83 : A) (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term48 A B GEN_PVAR_83 u f t x) = (term49 A B GEN_PVAR_83 u x f t).
Proof. exact (MK_COMB (@lem3488796 A GEN_PVAR_83) (@lem3488795 A B u x f t)). Qed.
Lemma lem3488798 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3488799 {A B : Type'} (GEN_PVAR_83 : A) (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term50 A B GEN_PVAR_83 u f t x) = (term51 A B GEN_PVAR_83 u f t x).
Proof. exact (MK_COMB (@lem3488797 A B GEN_PVAR_83 u x f t) (@lem3488798 A x)). Qed.
Lemma lem3488800 {A B : Type'} (GEN_PVAR_83 : A) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term52 A B GEN_PVAR_83 u f t) = (term53 A B GEN_PVAR_83 u f t).
Proof. exact (fun_ext (fun x : A => @lem3488799 A B GEN_PVAR_83 u f t x)). Qed.
Lemma lem3488801 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3488802 {A B : Type'} (GEN_PVAR_83 : A) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term54 A B GEN_PVAR_83 u f t) = (term55 A B GEN_PVAR_83 u f t).
Proof. exact (MK_COMB (@lem3488801 A) (@lem3488800 A B GEN_PVAR_83 u f t)). Qed.
Lemma lem3488803 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term56 A B u f t) = (term57 A B u f t).
Proof. exact (fun_ext (fun GEN_PVAR_83 : A => @lem3488802 A B GEN_PVAR_83 u f t)). Qed.
Lemma lem3488804 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3488805 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term58 A B u f t) = (term10 A B u f t).
Proof. exact (MK_COMB (@lem3488804 A) (@lem3488803 A B u f t)). Qed.
Lemma lem3488806 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3488807 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term44 A B x u f t) = (term59 A B x u f t).
Proof. exact (MK_COMB (@lem3488806 A x) (@lem3488805 A B u f t)). Qed.
Lemma lem3488808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3488809 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term60 A B x u f t) = (term61 A B x u f t).
Proof. exact (MK_COMB (@lem3488808) (@lem3488807 A B x u f t)). Qed.
Lemma lem3488810 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term45 A B u f t x) = (term47 A B u x f t).
Proof. exact (eq_refl (term45 A B u f t x)). Qed.
Lemma lem3488811 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : ((term44 A B x u f t) = (term45 A B u f t x)) = ((term59 A B x u f t) = (term47 A B u x f t)).
Proof. exact (MK_COMB (@lem3488809 A B x u f t) (@lem3488810 A B u x f t)). Qed.
Lemma lem3488812 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term59 A B x u f t) = (term47 A B u x f t).
Proof. exact (EQ_MP (@lem3488811 A B u x f t) (@lem3488794 A B u f t x)). Qed.
Lemma lem3488816 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488817 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488816 A P x). Qed.
Lemma lem3488818 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3488817 A u x). Qed.
Lemma lem3488819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488820 {A : Type'} (u : A -> Prop) (x : A) : (term62 A x u) = (term63 A u x).
Proof. exact (MK_COMB (@lem3488819) (@lem3488818 A u x)). Qed.
Lemma lem3488822 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3488823 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (@lem3488822 A B y f s). Qed.
Lemma lem3488824 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term66 A B x f t) = (term67 A B x f t).
Proof. exact (@lem3488823 A B (f x) f t). Qed.
Lemma lem3488834 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488835 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488834 A P x). Qed.
Lemma lem3488836 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3488835 A t x'). Qed.
Lemma lem3488837 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term68 A B x f x') = (term68 A B x f x').
Proof. exact (eq_refl (term68 A B x f x')). Qed.
Lemma lem3488838 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term69 A B x f x' t) = (term70 A B x f t x').
Proof. exact (MK_COMB (@lem3488837 A B x f x') (@lem3488836 A t x')). Qed.
Lemma lem3488841 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term71 A B x f t) = (term72 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3488838 A B x f t x')). Qed.
Lemma lem3488842 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3488843 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term67 A B x f t) = (term73 A B x f t).
Proof. exact (MK_COMB (@lem3488842 A) (@lem3488841 A B x f t)). Qed.
Lemma lem3488848 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term66 A B x f t) = (term73 A B x f t).
Proof. exact (TRANS (@lem3488824 A B x f t) (@lem3488843 A B x f t)). Qed.
Lemma lem3488849 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term47 A B u x f t) = (term74 A B u x f t).
Proof. exact (MK_COMB (@lem3488820 A u x) (@lem3488848 A B x f t)). Qed.
Lemma lem3488852 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term59 A B x u f t) = (term74 A B u x f t).
Proof. exact (TRANS (@lem3488812 A B u x f t) (@lem3488849 A B u x f t)). Qed.
Lemma lem3488853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3488854 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term75 A B x u f t) = (term76 A B u x f t).
Proof. exact (MK_COMB (@lem3488853) (@lem3488852 A B u x f t)). Qed.
Lemma lem3488856 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488856 A P x). Qed.
Lemma lem3488858 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3488857 A t x). Qed.
Lemma lem3488859 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term77 A B u f x t) = (term78 A B u f t x).
Proof. exact (MK_COMB (@lem3488854 A B u x f t) (@lem3488858 A t x)). Qed.
Lemma lem3488862 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term79 A B u f t) = (term80 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem3488859 A B u f t x)). Qed.
Lemma lem3488863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3488864 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term9 A B u f t) = (term81 A B u f t).
Proof. exact (MK_COMB (@lem3488863 A) (@lem3488862 A B u f t)). Qed.
Lemma lem3488869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488870 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term12 A B u f t) = (term82 A B u f t).
Proof. exact (MK_COMB (@lem3488869) (@lem3488864 A B u f t)). Qed.
Lemma lem3488878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488879 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488878 A P x). Qed.
Lemma lem3488880 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3488879 A s x). Qed.
Lemma lem3488881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3488882 {A : Type'} (s : A -> Prop) (x : A) : (term83 A x s) = (term84 A s x).
Proof. exact (MK_COMB (@lem3488881) (@lem3488880 A s x)). Qed.
Lemma lem3488884 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488884 A P x). Qed.
Lemma lem3488886 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3488885 A u x). Qed.
Lemma lem3488887 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term85 A s x u) = (term86 A s u x).
Proof. exact (MK_COMB (@lem3488882 A s x) (@lem3488886 A u x)). Qed.
Lemma lem3488890 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term87 A s u) = (term88 A s u).
Proof. exact (fun_ext (fun x : A => @lem3488887 A s u x)). Qed.
Lemma lem3488891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3488892 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term7 A s u) = (term89 A s u).
Proof. exact (MK_COMB (@lem3488891 A) (@lem3488890 A s u)). Qed.
Lemma lem3488897 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term14 A B f t s u) = (term90 A B f t s u).
Proof. exact (MK_COMB (@lem3488870 A B u f t) (@lem3488892 A s u)). Qed.
Lemma lem3488900 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term18 A B f t s u) = (term92 A B f t s u).
Proof. exact (MK_COMB (@lem3488782 A B f s t u) (@lem3488897 A B f t s u)). Qed.
Lemma lem3488903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3488904 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term20 A B f t s u) = (term93 A B f t s u).
Proof. exact (MK_COMB (@lem3488903) (@lem3488900 A B f t s u)). Qed.
Lemma lem3488912 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3488913 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (@lem3488912 A B y f s). Qed.
Lemma lem3488914 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term94 A B x f s t) = (term95 A B x f s t).
Proof. exact (@lem3488913 A B x f (@INTER A s t)). Qed.
Lemma lem3488924 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term96 A x s t) = (term97 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3488925 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term96 A x s t) = (term97 A s x t).
Proof. exact (@lem3488924 A s x t). Qed.
Lemma lem3488929 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488930 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488929 A P x). Qed.
Lemma lem3488931 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3488930 A s x). Qed.
Lemma lem3488932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488933 {A : Type'} (s : A -> Prop) (x : A) : (term62 A x s) = (term63 A s x).
Proof. exact (MK_COMB (@lem3488932) (@lem3488931 A s x)). Qed.
Lemma lem3488935 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488936 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488935 A P x). Qed.
Lemma lem3488937 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3488936 A t x). Qed.
Lemma lem3488938 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term97 A s x t) = (term98 A s t x).
Proof. exact (MK_COMB (@lem3488933 A s x) (@lem3488937 A t x)). Qed.
Lemma lem3488941 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term96 A x s t) = (term98 A s t x).
Proof. exact (TRANS (@lem3488925 A s x t) (@lem3488938 A s t x)). Qed.
Lemma lem3488942 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (term99 A B x f x').
Proof. exact (eq_refl (term99 A B x f x')). Qed.
Lemma lem3488943 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term100 A B x f x' s t) = (term101 A B x f s t x').
Proof. exact (MK_COMB (@lem3488942 A B x f x') (@lem3488941 A s t x')). Qed.
Lemma lem3488946 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term102 A B x f s t) = (term103 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3488943 A B x f s t x')). Qed.
Lemma lem3488947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3488948 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term95 A B x f s t) = (term104 A B x f s t).
Proof. exact (MK_COMB (@lem3488947 A) (@lem3488946 A B x f s t)). Qed.
Lemma lem3488953 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term94 A B x f s t) = (term104 A B x f s t).
Proof. exact (TRANS (@lem3488914 A B x f s t) (@lem3488948 A B x f s t)). Qed.
Lemma lem3488954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3488955 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term105 A B x f s t) = (term106 A B x f s t).
Proof. exact (MK_COMB (@lem3488954) (@lem3488953 A B x f s t)). Qed.
Lemma lem3488957 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term96 A x s t) = (term97 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3488958 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term96 B x s t) = (term97 B s x t).
Proof. exact (@lem3488957 B s x t). Qed.
Lemma lem3488959 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term107 A B x s f t) = (term108 A B s x f t).
Proof. exact (@lem3488958 B (@IMAGE A B f s) x (@IMAGE A B f t)). Qed.
Lemma lem3488963 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3488964 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (@lem3488963 A B y f s). Qed.
Lemma lem3488965 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term64 A B x f s) = (term65 A B x f s).
Proof. exact (@lem3488964 A B x f s). Qed.
Lemma lem3488975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3488976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3488975 A P x). Qed.
Lemma lem3488977 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3488976 A s x). Qed.
Lemma lem3488978 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (term99 A B x f x').
Proof. exact (eq_refl (term99 A B x f x')). Qed.
Lemma lem3488979 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term109 A B x f x' s) = (term110 A B x f s x').
Proof. exact (MK_COMB (@lem3488978 A B x f x') (@lem3488977 A s x')). Qed.
Lemma lem3488982 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term111 A B x f s) = (term112 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3488979 A B x f s x')). Qed.
Lemma lem3488983 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3488984 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term65 A B x f s) = (term113 A B x f s).
Proof. exact (MK_COMB (@lem3488983 A) (@lem3488982 A B x f s)). Qed.
Lemma lem3488989 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term64 A B x f s) = (term113 A B x f s).
Proof. exact (TRANS (@lem3488965 A B x f s) (@lem3488984 A B x f s)). Qed.
Lemma lem3488990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3488991 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term114 A B x f s) = (term115 A B x f s).
Proof. exact (MK_COMB (@lem3488990) (@lem3488989 A B x f s)). Qed.
Lemma lem3488993 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3488994 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term64 A B y f s) = (term65 A B y f s).
Proof. exact (@lem3488993 A B y f s). Qed.
Lemma lem3488995 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term64 A B x f t) = (term65 A B x f t).
Proof. exact (@lem3488994 A B x f t). Qed.
Lemma lem3489005 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3489006 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3489005 A P x). Qed.
Lemma lem3489007 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3489006 A t x). Qed.
Lemma lem3489008 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (term99 A B x f x').
Proof. exact (eq_refl (term99 A B x f x')). Qed.
Lemma lem3489009 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term109 A B x f x' t) = (term110 A B x f t x').
Proof. exact (MK_COMB (@lem3489008 A B x f x') (@lem3489007 A t x')). Qed.
Lemma lem3489012 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term111 A B x f t) = (term112 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3489009 A B x f t x')). Qed.
Lemma lem3489013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489014 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term65 A B x f t) = (term113 A B x f t).
Proof. exact (MK_COMB (@lem3489013 A) (@lem3489012 A B x f t)). Qed.
Lemma lem3489019 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term64 A B x f t) = (term113 A B x f t).
Proof. exact (TRANS (@lem3488995 A B x f t) (@lem3489014 A B x f t)). Qed.
Lemma lem3489020 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term108 A B s x f t) = (term116 A B s x f t).
Proof. exact (MK_COMB (@lem3488991 A B x f s) (@lem3489019 A B x f t)). Qed.
Lemma lem3489023 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term107 A B x s f t) = (term116 A B s x f t).
Proof. exact (TRANS (@lem3488959 A B s x f t) (@lem3489020 A B s x f t)). Qed.
Lemma lem3489024 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term94 A B x f s t) = (term107 A B x s f t)) = ((term104 A B x f s t) = (term116 A B s x f t)).
Proof. exact (MK_COMB (@lem3488955 A B x f s t) (@lem3489023 A B s x f t)). Qed.
Lemma lem3489027 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term117 A B s f t) = (term118 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3489024 A B s x f t)). Qed.
Lemma lem3489028 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3489029 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term24 A B s f t) = (term119 A B s f t).
Proof. exact (MK_COMB (@lem3489028 B) (@lem3489027 A B s f t)). Qed.
Lemma lem3489034 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term26 A B u s f t) = (term120 A B u s f t).
Proof. exact (MK_COMB (@lem3488904 A B f t s u) (@lem3489029 A B s f t)). Qed.
Lemma lem3489037 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term28 A B s f t) = (term121 A B s f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3489034 A B u s f t)). Qed.
Lemma lem3489038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3489039 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term30 A B s f t) = (term122 A B s f t).
Proof. exact (MK_COMB (@lem3489038 A) (@lem3489037 A B s f t)). Qed.
Lemma lem3489044 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term32 A B s f) = (term123 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3489039 A B s f t)). Qed.
Lemma lem3489045 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3489046 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term34 A B s f) = (term124 A B s f).
Proof. exact (MK_COMB (@lem3489045 A) (@lem3489044 A B s f)). Qed.
Lemma lem3489051 {A B : Type'} (f : A -> B) : (term36 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3489046 A B s f)). Qed.
Lemma lem3489052 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3489053 {A B : Type'} (f : A -> B) : (term38 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem3489052 A) (@lem3489051 A B f)). Qed.
Lemma lem3489058 {A B : Type'} : (term40 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3489053 A B f)). Qed.
Lemma lem3489059 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3489060 {A B : Type'} : (term42 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem3489059 A B) (@lem3489058 A B)). Qed.
Lemma lem3489065 {A B : Type'} : (term128 A B) = (term42 A B).
Proof. exact (SYM (@lem3489060 A B)). Qed.
Lemma lem3489067 (p : Prop) : p = (term129 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3489068 {A B : Type'} : (term128 A B) = (term130 A B).
Proof. exact (@lem3489067 (term128 A B)). Qed.
Lemma lem3489069 {A B : Type'} : (term130 A B) = (term128 A B).
Proof. exact (SYM (@lem3489068 A B)). Qed.
Lemma lem3489070 {A B : Type'} (h1 : term131 A B) : term131 A B.
Proof. exact (h1). Qed.
Lemma lem3489073 {A B : Type'} (h1 : term130 A B) : term130 A B.
Proof. exact (h1). Qed.
Lemma lem3489074 {A B : Type'} : term132 A B.
Proof. exact (fun h0 : term130 A B => @lem3489073 A B h0). Qed.
Lemma lem3489075 {A B : Type'} (h1 : term132 A B) : term132 A B.
Proof. exact (h1). Qed.
Lemma lem3489076 {A B : Type'} (h1 : term130 A B) : term130 A B.
Proof. exact (h1). Qed.
Lemma lem3489077 {A B : Type'} (h1 : term130 A B) (h2 : term132 A B) : term130 A B.
Proof. exact (@lem3489075 A B h2 (@lem3489076 A B h1)). Qed.
Lemma lem3489078 {A B : Type'} (h1 : term130 A B) : term133 A B.
Proof. exact (fun h0 : term132 A B => @lem3489077 A B h1 h0). Qed.
Lemma lem3489079 {A B : Type'} (h1 : term132 A B) : term132 A B.
Proof. exact (h1). Qed.
Lemma lem3489080 {A B : Type'} (h1 : term130 A B) (h2 : term132 A B) : term130 A B.
Proof. exact (@lem3489078 A B h1 (@lem3489079 A B h2)). Qed.
Lemma lem3489081 {A B : Type'} (h1 : term132 A B) : term132 A B.
Proof. exact (fun h0 : term130 A B => @lem3489080 A B h0 h1). Qed.
Lemma lem3489082 {A B : Type'} : term134 A B.
Proof. exact (fun h0 : term132 A B => @lem3489081 A B h0). Qed.
Lemma lem3489085 {A B : Type'} : term132 A B.
Proof. exact (@lem3489082 A B (@lem3489074 A B)). Qed.
Lemma lem3489086 {A B : Type'} : term132 A B.
Proof. exact (@lem3489085 A B). Qed.
Lemma lem3489088 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3489089 {A B : Type'} : (term130 A B) = (term135 A B).
Proof. exact (@lem3489088 (term131 A B)). Qed.
Lemma lem3489091 (t : Prop) : (term136 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3489092 {A B : Type'} : (term135 A B) = (term128 A B).
Proof. exact (@lem3489091 (term128 A B)). Qed.
Lemma lem3489343 {A B : Type'} : (term130 A B) = (term128 A B).
Proof. exact (TRANS (@lem3489089 A B) (@lem3489092 A B)). Qed.
Lemma lem3489348 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term110 A B x f t x') = (term110 A B x f t x').
Proof. exact (eq_refl (term110 A B x f t x')). Qed.
Lemma lem3489349 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term112 A B x f t) = (term112 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3489348 A B x f t x')). Qed.
Lemma lem3489350 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489351 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term113 A B x f t) = (term113 A B x f t).
Proof. exact (MK_COMB (@lem3489350 A) (@lem3489349 A B x f t)). Qed.
Lemma lem3489356 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term110 A B x f s x') = (term110 A B x f s x').
Proof. exact (eq_refl (term110 A B x f s x')). Qed.
Lemma lem3489357 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term112 A B x f s) = (term112 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3489356 A B x f s x')). Qed.
Lemma lem3489358 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489359 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term113 A B x f s) = (term113 A B x f s).
Proof. exact (MK_COMB (@lem3489358 A) (@lem3489357 A B x f s)). Qed.
Lemma lem3489360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3489361 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term115 A B x f s) = (term115 A B x f s).
Proof. exact (MK_COMB (@lem3489360) (@lem3489359 A B x f s)). Qed.
Lemma lem3489362 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term116 A B s x f t) = (term116 A B s x f t).
Proof. exact (MK_COMB (@lem3489361 A B x f s) (@lem3489351 A B x f t)). Qed.
Lemma lem3489371 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term101 A B x f s t x') = (term101 A B x f s t x').
Proof. exact (eq_refl (term101 A B x f s t x')). Qed.
Lemma lem3489372 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term103 A B x f s t) = (term103 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3489371 A B x f s t x')). Qed.
Lemma lem3489373 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489374 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term104 A B x f s t) = (term104 A B x f s t).
Proof. exact (MK_COMB (@lem3489373 A) (@lem3489372 A B x f s t)). Qed.
Lemma lem3489375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3489376 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term106 A B x f s t) = (term106 A B x f s t).
Proof. exact (MK_COMB (@lem3489375) (@lem3489374 A B x f s t)). Qed.
Lemma lem3489377 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term104 A B x f s t) = (term116 A B s x f t)) = ((term104 A B x f s t) = (term116 A B s x f t)).
Proof. exact (MK_COMB (@lem3489376 A B x f s t) (@lem3489362 A B s x f t)). Qed.
Lemma lem3489378 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term118 A B s f t) = (term118 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3489377 A B s x f t)). Qed.
Lemma lem3489379 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3489380 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term119 A B s f t) = (term119 A B s f t).
Proof. exact (MK_COMB (@lem3489379 B) (@lem3489378 A B s f t)). Qed.
Lemma lem3489385 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term86 A s u x) = (term86 A s u x).
Proof. exact (eq_refl (term86 A s u x)). Qed.
Lemma lem3489386 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term88 A s u) = (term88 A s u).
Proof. exact (fun_ext (fun x : A => @lem3489385 A s u x)). Qed.
Lemma lem3489387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489388 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term89 A s u) = (term89 A s u).
Proof. exact (MK_COMB (@lem3489387 A) (@lem3489386 A s u)). Qed.
Lemma lem3489389 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3489394 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term70 A B x f t x') = (term70 A B x f t x').
Proof. exact (eq_refl (term70 A B x f t x')). Qed.
Lemma lem3489395 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term72 A B x f t) = (term72 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3489394 A B x f t x')). Qed.
Lemma lem3489396 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489397 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term73 A B x f t) = (term73 A B x f t).
Proof. exact (MK_COMB (@lem3489396 A) (@lem3489395 A B x f t)). Qed.
Lemma lem3489400 {A : Type'} (u : A -> Prop) (x : A) : (term63 A u x) = (term63 A u x).
Proof. exact (eq_refl (term63 A u x)). Qed.
Lemma lem3489401 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term74 A B u x f t) = (term74 A B u x f t).
Proof. exact (MK_COMB (@lem3489400 A u x) (@lem3489397 A B x f t)). Qed.
Lemma lem3489402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3489403 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term76 A B u x f t) = (term76 A B u x f t).
Proof. exact (MK_COMB (@lem3489402) (@lem3489401 A B u x f t)). Qed.
Lemma lem3489404 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term78 A B u f t x) = (term78 A B u f t x).
Proof. exact (MK_COMB (@lem3489403 A B u x f t) (@lem3489389 A t x)). Qed.
Lemma lem3489405 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term80 A B u f t) = (term80 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem3489404 A B u f t x)). Qed.
Lemma lem3489406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489407 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term81 A B u f t) = (term81 A B u f t).
Proof. exact (MK_COMB (@lem3489406 A) (@lem3489405 A B u f t)). Qed.
Lemma lem3489408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3489409 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term82 A B u f t) = (term82 A B u f t).
Proof. exact (MK_COMB (@lem3489408) (@lem3489407 A B u f t)). Qed.
Lemma lem3489410 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term90 A B f t s u) = (term90 A B f t s u).
Proof. exact (MK_COMB (@lem3489409 A B u f t) (@lem3489388 A s u)). Qed.
Lemma lem3489415 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term86 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3489416 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term88 A t u) = (term88 A t u).
Proof. exact (fun_ext (fun x : A => @lem3489415 A t u x)). Qed.
Lemma lem3489417 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489418 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term89 A t u) = (term89 A t u).
Proof. exact (MK_COMB (@lem3489417 A) (@lem3489416 A t u)). Qed.
Lemma lem3489419 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3489424 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term70 A B x f s x') = (term70 A B x f s x').
Proof. exact (eq_refl (term70 A B x f s x')). Qed.
Lemma lem3489425 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term72 A B x f s) = (term72 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3489424 A B x f s x')). Qed.
Lemma lem3489426 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489427 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term73 A B x f s) = (term73 A B x f s).
Proof. exact (MK_COMB (@lem3489426 A) (@lem3489425 A B x f s)). Qed.
Lemma lem3489430 {A : Type'} (u : A -> Prop) (x : A) : (term63 A u x) = (term63 A u x).
Proof. exact (eq_refl (term63 A u x)). Qed.
Lemma lem3489431 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term74 A B u x f s) = (term74 A B u x f s).
Proof. exact (MK_COMB (@lem3489430 A u x) (@lem3489427 A B x f s)). Qed.
Lemma lem3489432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3489433 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term76 A B u x f s) = (term76 A B u x f s).
Proof. exact (MK_COMB (@lem3489432) (@lem3489431 A B u x f s)). Qed.
Lemma lem3489434 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term78 A B u f s x) = (term78 A B u f s x).
Proof. exact (MK_COMB (@lem3489433 A B u x f s) (@lem3489419 A s x)). Qed.
Lemma lem3489435 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term80 A B u f s) = (term80 A B u f s).
Proof. exact (fun_ext (fun x : A => @lem3489434 A B u f s x)). Qed.
Lemma lem3489436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489437 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B u f s) = (term81 A B u f s).
Proof. exact (MK_COMB (@lem3489436 A) (@lem3489435 A B u f s)). Qed.
Lemma lem3489438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3489439 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term82 A B u f s) = (term82 A B u f s).
Proof. exact (MK_COMB (@lem3489438) (@lem3489437 A B u f s)). Qed.
Lemma lem3489440 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term90 A B f s t u) = (term90 A B f s t u).
Proof. exact (MK_COMB (@lem3489439 A B u f s) (@lem3489418 A t u)). Qed.
Lemma lem3489441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3489442 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term91 A B f s t u) = (term91 A B f s t u).
Proof. exact (MK_COMB (@lem3489441) (@lem3489440 A B f s t u)). Qed.
Lemma lem3489443 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term92 A B f t s u) = (term92 A B f t s u).
Proof. exact (MK_COMB (@lem3489442 A B f s t u) (@lem3489410 A B f t s u)). Qed.
Lemma lem3489444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3489445 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term93 A B f t s u) = (term93 A B f t s u).
Proof. exact (MK_COMB (@lem3489444) (@lem3489443 A B f t s u)). Qed.
Lemma lem3489446 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term120 A B u s f t) = (term120 A B u s f t).
Proof. exact (MK_COMB (@lem3489445 A B f t s u) (@lem3489380 A B s f t)). Qed.
Lemma lem3489447 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term121 A B s f t) = (term121 A B s f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3489446 A B u s f t)). Qed.
Lemma lem3489448 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3489449 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term122 A B s f t) = (term122 A B s f t).
Proof. exact (MK_COMB (@lem3489448 A) (@lem3489447 A B s f t)). Qed.
Lemma lem3489450 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term123 A B s f) = (term123 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3489449 A B s f t)). Qed.
Lemma lem3489451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3489452 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term124 A B s f) = (term124 A B s f).
Proof. exact (MK_COMB (@lem3489451 A) (@lem3489450 A B s f)). Qed.
Lemma lem3489453 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3489452 A B s f)). Qed.
Lemma lem3489454 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3489455 {A B : Type'} (f : A -> B) : (term126 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem3489454 A) (@lem3489453 A B f)). Qed.
Lemma lem3489456 {A B : Type'} : (term127 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3489455 A B f)). Qed.
Lemma lem3489457 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3489458 {A B : Type'} : (term128 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem3489457 A B) (@lem3489456 A B)). Qed.
Lemma lem3489579 {A B : Type'} : (term130 A B) = (term128 A B).
Proof. exact (TRANS (@lem3489343 A B) (@lem3489458 A B)). Qed.
Lemma lem3489580 {A B : Type'} : (term128 A B) = (term130 A B).
Proof. exact (SYM (@lem3489579 A B)). Qed.
Lemma lem3489581 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term92 A B f t s u) : term92 A B f t s u.
Proof. exact (h1). Qed.
Lemma lem3489583 (p : Prop) : p = (term129 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3489584 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term104 A B x f s t) = (term116 A B s x f t)) = (term137 A B s x f t).
Proof. exact (@lem3489583 ((term104 A B x f s t) = (term116 A B s x f t))). Qed.
Lemma lem3489585 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term137 A B s x f t) = ((term104 A B x f s t) = (term116 A B s x f t)).
Proof. exact (SYM (@lem3489584 A B s x f t)). Qed.
Lemma lem3489586 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term138 A B s x f t) : term138 A B s x f t.
Proof. exact (h1). Qed.
Lemma lem3489594 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term139 A B x f s x') = (term140 A B x f s x').
Proof. exact (@lem17045 ((f x) = (f x')) (s x')). Qed.
Lemma lem3489595 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3489596 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term143 A B x f s) = (term144 A B x f s).
Proof. exact (@lem3489595 A (term72 A B x f s)). Qed.
Lemma lem3489597 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term145 A B x f s x') = (term70 A B x f s x').
Proof. exact (eq_refl (term145 A B x f s x')). Qed.
Lemma lem3489598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3489599 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term139 A B x f s x').
Proof. exact (MK_COMB (@lem3489598) (@lem3489597 A B x f s x')). Qed.
Lemma lem3489600 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term140 A B x f s x').
Proof. exact (TRANS (@lem3489599 A B x f s x') (@lem3489594 A B x f s x')). Qed.
Lemma lem3489601 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term147 A B x f s) = (term148 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3489600 A B x f s x')). Qed.
Lemma lem3489602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489603 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term144 A B x f s) = (term149 A B x f s).
Proof. exact (MK_COMB (@lem3489602 A) (@lem3489601 A B x f s)). Qed.
Lemma lem3489604 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term143 A B x f s) = (term149 A B x f s).
Proof. exact (TRANS (@lem3489596 A B x f s) (@lem3489603 A B x f s)). Qed.
Lemma lem3489606 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3489607 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term151 A B u x f s) = (term152 A B u x f s).
Proof. exact (MK_COMB (@lem3489606 A u x) (@lem3489604 A B x f s)). Qed.
Lemma lem3489608 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term153 A B u x f s) = (term151 A B u x f s).
Proof. exact (@lem17045 (u x) (term73 A B x f s)). Qed.
Lemma lem3489609 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term153 A B u x f s) = (term152 A B u x f s).
Proof. exact (TRANS (@lem3489608 A B u x f s) (@lem3489607 A B u x f s)). Qed.
Lemma lem3489610 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3489611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3489612 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term154 A B u x f s) = (term155 A B u x f s).
Proof. exact (MK_COMB (@lem3489611) (@lem3489609 A B u x f s)). Qed.
Lemma lem3489613 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term156 A B u f s x) = (term157 A B u f s x).
Proof. exact (MK_COMB (@lem3489612 A B u x f s) (@lem3489610 A s x)). Qed.
Lemma lem3489614 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term78 A B u f s x) = (term156 A B u f s x).
Proof. exact (@lem17265 (term74 A B u x f s) (s x)). Qed.
Lemma lem3489615 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term78 A B u f s x) = (term157 A B u f s x).
Proof. exact (TRANS (@lem3489614 A B u f s x) (@lem3489613 A B u f s x)). Qed.
Lemma lem3489616 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term80 A B u f s) = (term158 A B u f s).
Proof. exact (fun_ext (fun x : A => @lem3489615 A B u f s x)). Qed.
Lemma lem3489617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489618 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B u f s) = (term159 A B u f s).
Proof. exact (MK_COMB (@lem3489617 A) (@lem3489616 A B u f s)). Qed.
Lemma lem3489625 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term160 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3489626 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term88 A t u) = (term161 A t u).
Proof. exact (fun_ext (fun x : A => @lem3489625 A t u x)). Qed.
Lemma lem3489627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489628 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term89 A t u) = (term162 A t u).
Proof. exact (MK_COMB (@lem3489627 A) (@lem3489626 A t u)). Qed.
Lemma lem3489629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3489630 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term82 A B u f s) = (term163 A B u f s).
Proof. exact (MK_COMB (@lem3489629) (@lem3489618 A B u f s)). Qed.
Lemma lem3489631 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term90 A B f s t u) = (term164 A B f s t u).
Proof. exact (MK_COMB (@lem3489630 A B u f s) (@lem3489628 A t u)). Qed.
Lemma lem3489639 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term139 A B x f t x') = (term140 A B x f t x').
Proof. exact (@lem17045 ((f x) = (f x')) (t x')). Qed.
Lemma lem3489640 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3489641 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term143 A B x f t) = (term144 A B x f t).
Proof. exact (@lem3489640 A (term72 A B x f t)). Qed.
Lemma lem3489642 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term145 A B x f t x') = (term70 A B x f t x').
Proof. exact (eq_refl (term145 A B x f t x')). Qed.
Lemma lem3489643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3489644 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term146 A B x f t x') = (term139 A B x f t x').
Proof. exact (MK_COMB (@lem3489643) (@lem3489642 A B x f t x')). Qed.
Lemma lem3489645 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term146 A B x f t x') = (term140 A B x f t x').
Proof. exact (TRANS (@lem3489644 A B x f t x') (@lem3489639 A B x f t x')). Qed.
Lemma lem3489646 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term147 A B x f t) = (term148 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3489645 A B x f t x')). Qed.
Lemma lem3489647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489648 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term144 A B x f t) = (term149 A B x f t).
Proof. exact (MK_COMB (@lem3489647 A) (@lem3489646 A B x f t)). Qed.
Lemma lem3489649 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term143 A B x f t) = (term149 A B x f t).
Proof. exact (TRANS (@lem3489641 A B x f t) (@lem3489648 A B x f t)). Qed.
Lemma lem3489651 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3489652 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term151 A B u x f t) = (term152 A B u x f t).
Proof. exact (MK_COMB (@lem3489651 A u x) (@lem3489649 A B x f t)). Qed.
Lemma lem3489653 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term153 A B u x f t) = (term151 A B u x f t).
Proof. exact (@lem17045 (u x) (term73 A B x f t)). Qed.
Lemma lem3489654 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term153 A B u x f t) = (term152 A B u x f t).
Proof. exact (TRANS (@lem3489653 A B u x f t) (@lem3489652 A B u x f t)). Qed.
Lemma lem3489655 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3489656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3489657 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term154 A B u x f t) = (term155 A B u x f t).
Proof. exact (MK_COMB (@lem3489656) (@lem3489654 A B u x f t)). Qed.
Lemma lem3489658 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term156 A B u f t x) = (term157 A B u f t x).
Proof. exact (MK_COMB (@lem3489657 A B u x f t) (@lem3489655 A t x)). Qed.
Lemma lem3489659 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term78 A B u f t x) = (term156 A B u f t x).
Proof. exact (@lem17265 (term74 A B u x f t) (t x)). Qed.
Lemma lem3489660 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term78 A B u f t x) = (term157 A B u f t x).
Proof. exact (TRANS (@lem3489659 A B u f t x) (@lem3489658 A B u f t x)). Qed.
Lemma lem3489661 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term80 A B u f t) = (term158 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem3489660 A B u f t x)). Qed.
Lemma lem3489662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489663 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term81 A B u f t) = (term159 A B u f t).
Proof. exact (MK_COMB (@lem3489662 A) (@lem3489661 A B u f t)). Qed.
Lemma lem3489670 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term86 A s u x) = (term160 A s u x).
Proof. exact (@lem17265 (s x) (u x)). Qed.
Lemma lem3489671 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term88 A s u) = (term161 A s u).
Proof. exact (fun_ext (fun x : A => @lem3489670 A s u x)). Qed.
Lemma lem3489672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489673 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term89 A s u) = (term162 A s u).
Proof. exact (MK_COMB (@lem3489672 A) (@lem3489671 A s u)). Qed.
Lemma lem3489674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3489675 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term82 A B u f t) = (term163 A B u f t).
Proof. exact (MK_COMB (@lem3489674) (@lem3489663 A B u f t)). Qed.
Lemma lem3489676 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term90 A B f t s u) = (term164 A B f t s u).
Proof. exact (MK_COMB (@lem3489675 A B u f t) (@lem3489673 A s u)). Qed.
Lemma lem3489677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3489678 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term91 A B f s t u) = (term165 A B f s t u).
Proof. exact (MK_COMB (@lem3489677) (@lem3489631 A B f s t u)). Qed.
Lemma lem3489907 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term92 A B f t s u) = (term166 A B f t s u).
Proof. exact (MK_COMB (@lem3489678 A B f s t u) (@lem3489676 A B f t s u)). Qed.
Lemma lem3489908 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term92 A B f t s u) : term166 A B f t s u.
Proof. exact (EQ_MP (@lem3489907 A B f t s u) (@lem3489581 A B f t s u h1)). Qed.
Lemma lem3489919 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term167 A s t x) = (term168 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3489924 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term169 A B x f x') = (term169 A B x f x').
Proof. exact (eq_refl (term169 A B x f x')). Qed.
Lemma lem3489925 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term170 A B x f s t x') = (term171 A B x f s t x').
Proof. exact (MK_COMB (@lem3489924 A B x f x') (@lem3489919 A s t x')). Qed.
Lemma lem3489926 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term172 A B x f s t x') = (term170 A B x f s t x').
Proof. exact (@lem17045 (x = (f x')) (term98 A s t x')). Qed.
Lemma lem3489927 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term172 A B x f s t x') = (term171 A B x f s t x').
Proof. exact (TRANS (@lem3489926 A B x f s t x') (@lem3489925 A B x f s t x')). Qed.
Lemma lem3489930 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term101 A B x f s t x') = (term101 A B x f s t x').
Proof. exact (eq_refl (term101 A B x f s t x')). Qed.
Lemma lem3489931 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3489932 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term173 A B x f s t) = (term174 A B x f s t).
Proof. exact (@lem3489931 A (term103 A B x f s t)). Qed.
Lemma lem3489933 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A B x f s t x') = (term101 A B x f s t x').
Proof. exact (eq_refl (term175 A B x f s t x')). Qed.
Lemma lem3489934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3489935 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term176 A B x f s t x') = (term172 A B x f s t x').
Proof. exact (MK_COMB (@lem3489934) (@lem3489933 A B x f s t x')). Qed.
Lemma lem3489936 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term176 A B x f s t x') = (term171 A B x f s t x').
Proof. exact (TRANS (@lem3489935 A B x f s t x') (@lem3489927 A B x f s t x')). Qed.
Lemma lem3489937 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term177 A B x f s t) = (term178 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3489936 A B x f s t x')). Qed.
Lemma lem3489938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489939 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term174 A B x f s t) = (term179 A B x f s t).
Proof. exact (MK_COMB (@lem3489938 A) (@lem3489937 A B x f s t)). Qed.
Lemma lem3489940 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term173 A B x f s t) = (term179 A B x f s t).
Proof. exact (TRANS (@lem3489932 A B x f s t) (@lem3489939 A B x f s t)). Qed.
Lemma lem3489941 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term103 A B x f s t) = (term103 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3489930 A B x f s t x')). Qed.
Lemma lem3489942 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489943 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term104 A B x f s t) = (term104 A B x f s t).
Proof. exact (MK_COMB (@lem3489942 A) (@lem3489941 A B x f s t)). Qed.
Lemma lem3489952 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term181 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3489955 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term110 A B x f s x') = (term110 A B x f s x').
Proof. exact (eq_refl (term110 A B x f s x')). Qed.
Lemma lem3489956 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3489957 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term182 A B x f s) = (term183 A B x f s).
Proof. exact (@lem3489956 A (term112 A B x f s)). Qed.
Lemma lem3489958 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term184 A B x f s x') = (term110 A B x f s x').
Proof. exact (eq_refl (term184 A B x f s x')). Qed.
Lemma lem3489959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3489960 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term185 A B x f s x') = (term180 A B x f s x').
Proof. exact (MK_COMB (@lem3489959) (@lem3489958 A B x f s x')). Qed.
Lemma lem3489961 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term185 A B x f s x') = (term181 A B x f s x').
Proof. exact (TRANS (@lem3489960 A B x f s x') (@lem3489952 A B x f s x')). Qed.
Lemma lem3489962 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term186 A B x f s) = (term187 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3489961 A B x f s x')). Qed.
Lemma lem3489963 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489964 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term183 A B x f s) = (term188 A B x f s).
Proof. exact (MK_COMB (@lem3489963 A) (@lem3489962 A B x f s)). Qed.
Lemma lem3489965 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term182 A B x f s) = (term188 A B x f s).
Proof. exact (TRANS (@lem3489957 A B x f s) (@lem3489964 A B x f s)). Qed.
Lemma lem3489966 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term112 A B x f s) = (term112 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3489955 A B x f s x')). Qed.
Lemma lem3489967 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489968 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term113 A B x f s) = (term113 A B x f s).
Proof. exact (MK_COMB (@lem3489967 A) (@lem3489966 A B x f s)). Qed.
Lemma lem3489977 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term180 A B x f t x') = (term181 A B x f t x').
Proof. exact (@lem17045 (x = (f x')) (t x')). Qed.
Lemma lem3489980 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term110 A B x f t x') = (term110 A B x f t x').
Proof. exact (eq_refl (term110 A B x f t x')). Qed.
Lemma lem3489981 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3489982 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term182 A B x f t) = (term183 A B x f t).
Proof. exact (@lem3489981 A (term112 A B x f t)). Qed.
Lemma lem3489983 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term184 A B x f t x') = (term110 A B x f t x').
Proof. exact (eq_refl (term184 A B x f t x')). Qed.
Lemma lem3489984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3489985 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term185 A B x f t x') = (term180 A B x f t x').
Proof. exact (MK_COMB (@lem3489984) (@lem3489983 A B x f t x')). Qed.
Lemma lem3489986 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term185 A B x f t x') = (term181 A B x f t x').
Proof. exact (TRANS (@lem3489985 A B x f t x') (@lem3489977 A B x f t x')). Qed.
Lemma lem3489987 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term186 A B x f t) = (term187 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3489986 A B x f t x')). Qed.
Lemma lem3489988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3489989 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term183 A B x f t) = (term188 A B x f t).
Proof. exact (MK_COMB (@lem3489988 A) (@lem3489987 A B x f t)). Qed.
Lemma lem3489990 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term182 A B x f t) = (term188 A B x f t).
Proof. exact (TRANS (@lem3489982 A B x f t) (@lem3489989 A B x f t)). Qed.
Lemma lem3489991 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term112 A B x f t) = (term112 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3489980 A B x f t x')). Qed.
Lemma lem3489992 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3489993 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term113 A B x f t) = (term113 A B x f t).
Proof. exact (MK_COMB (@lem3489992 A) (@lem3489991 A B x f t)). Qed.
Lemma lem3489994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3489995 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term189 A B x f s) = (term190 A B x f s).
Proof. exact (MK_COMB (@lem3489994) (@lem3489965 A B x f s)). Qed.
Lemma lem3489996 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term191 A B s x f t) = (term192 A B s x f t).
Proof. exact (MK_COMB (@lem3489995 A B x f s) (@lem3489990 A B x f t)). Qed.
Lemma lem3489997 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term193 A B s x f t) = (term191 A B s x f t).
Proof. exact (@lem17045 (term113 A B x f s) (term113 A B x f t)). Qed.
Lemma lem3489998 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term193 A B s x f t) = (term192 A B s x f t).
Proof. exact (TRANS (@lem3489997 A B s x f t) (@lem3489996 A B s x f t)). Qed.
Lemma lem3489999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490000 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term115 A B x f s) = (term115 A B x f s).
Proof. exact (MK_COMB (@lem3489999) (@lem3489968 A B x f s)). Qed.
Lemma lem3490001 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term116 A B s x f t) = (term116 A B s x f t).
Proof. exact (MK_COMB (@lem3490000 A B x f s) (@lem3489993 A B x f t)). Qed.
Lemma lem3490002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490003 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term194 A B x f s t) = (term195 A B x f s t).
Proof. exact (MK_COMB (@lem3490002) (@lem3489940 A B x f s t)). Qed.
Lemma lem3490004 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term196 A B s x f t) = (term197 A B s x f t).
Proof. exact (MK_COMB (@lem3490003 A B x f s t) (@lem3490001 A B s x f t)). Qed.
Lemma lem3490005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490006 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term198 A B x f s t) = (term198 A B x f s t).
Proof. exact (MK_COMB (@lem3490005) (@lem3489943 A B x f s t)). Qed.
Lemma lem3490007 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term199 A B s x f t) = (term200 A B s x f t).
Proof. exact (MK_COMB (@lem3490006 A B x f s t) (@lem3489998 A B s x f t)). Qed.
Lemma lem3490008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490009 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term201 A B s x f t) = (term202 A B s x f t).
Proof. exact (MK_COMB (@lem3490008) (@lem3490007 A B s x f t)). Qed.
Lemma lem3490010 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term203 A B s x f t) = (term204 A B s x f t).
Proof. exact (MK_COMB (@lem3490009 A B s x f t) (@lem3490004 A B s x f t)). Qed.
Lemma lem3490011 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term138 A B s x f t) = (term203 A B s x f t).
Proof. exact (@lem17646 (term104 A B x f s t) (term116 A B s x f t)). Qed.
Lemma lem3490012 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term138 A B s x f t) = (term204 A B s x f t).
Proof. exact (TRANS (@lem3490011 A B s x f t) (@lem3490010 A B s x f t)). Qed.
Lemma lem3490271 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3490272 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (@lem3490271 A P Q). Qed.
Lemma lem3490273 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term207 A B s x f t) = (term208 A B s x f t).
Proof. exact (@lem3490272 A (term103 A B x f s t) (term192 A B s x f t)). Qed.
Lemma lem3490274 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A B x f s t x') = (term101 A B x f s t x').
Proof. exact (eq_refl (term175 A B x f s t x')). Qed.
Lemma lem3490275 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term209 A B x f s t) = (term103 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3490274 A B x f s t x')). Qed.
Lemma lem3490276 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490277 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term210 A B x f s t) = (term104 A B x f s t).
Proof. exact (MK_COMB (@lem3490276 A) (@lem3490275 A B x f s t)). Qed.
Lemma lem3490278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490279 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term211 A B x f s t) = (term198 A B x f s t).
Proof. exact (MK_COMB (@lem3490278) (@lem3490277 A B x f s t)). Qed.
Lemma lem3490280 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term192 A B s x f t) = (term192 A B s x f t).
Proof. exact (eq_refl (term192 A B s x f t)). Qed.
Lemma lem3490281 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term207 A B s x f t) = (term200 A B s x f t).
Proof. exact (MK_COMB (@lem3490279 A B x f s t) (@lem3490280 A B s x f t)). Qed.
Lemma lem3490282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490283 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term212 A B s x f t) = (term213 A B s x f t).
Proof. exact (MK_COMB (@lem3490282) (@lem3490281 A B s x f t)). Qed.
Lemma lem3490284 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A B x f s t x') = (term101 A B x f s t x').
Proof. exact (eq_refl (term175 A B x f s t x')). Qed.
Lemma lem3490285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490286 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term214 A B x f s t x') = (term215 A B x f s t x').
Proof. exact (MK_COMB (@lem3490285) (@lem3490284 A B x f s t x')). Qed.
Lemma lem3490287 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term192 A B s x f t) = (term192 A B s x f t).
Proof. exact (eq_refl (term192 A B s x f t)). Qed.
Lemma lem3490288 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term216 A B x s x' f t) = (term217 A B x s x' f t).
Proof. exact (MK_COMB (@lem3490286 A B x' f s t x) (@lem3490287 A B s x' f t)). Qed.
Lemma lem3490289 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term218 A B s x f t) = (term219 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490288 A B x' s x f t)). Qed.
Lemma lem3490290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490291 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term208 A B s x f t) = (term220 A B s x f t).
Proof. exact (MK_COMB (@lem3490290 A) (@lem3490289 A B s x f t)). Qed.
Lemma lem3490292 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term207 A B s x f t) = (term208 A B s x f t)) = ((term200 A B s x f t) = (term220 A B s x f t)).
Proof. exact (MK_COMB (@lem3490283 A B s x f t) (@lem3490291 A B s x f t)). Qed.
Lemma lem3490293 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term200 A B s x f t) = (term220 A B s x f t).
Proof. exact (EQ_MP (@lem3490292 A B s x f t) (@lem3490273 A B s x f t)). Qed.
Lemma lem3490294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490295 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term202 A B s x f t) = (term221 A B s x f t).
Proof. exact (MK_COMB (@lem3490294) (@lem3490293 A B s x f t)). Qed.
Lemma lem3490297 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3490298 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (@lem3490297 A P Q). Qed.
Lemma lem3490299 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term222 A B s x f t) = (term223 A B s x f t).
Proof. exact (@lem3490298 A (term112 A B x f s) (term113 A B x f t)). Qed.
Lemma lem3490300 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term184 A B x f s x') = (term110 A B x f s x').
Proof. exact (eq_refl (term184 A B x f s x')). Qed.
Lemma lem3490301 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term224 A B x f s) = (term112 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3490300 A B x f s x')). Qed.
Lemma lem3490302 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490303 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term225 A B x f s) = (term113 A B x f s).
Proof. exact (MK_COMB (@lem3490302 A) (@lem3490301 A B x f s)). Qed.
Lemma lem3490304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490305 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term226 A B x f s) = (term115 A B x f s).
Proof. exact (MK_COMB (@lem3490304) (@lem3490303 A B x f s)). Qed.
Lemma lem3490306 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term113 A B x f t) = (term113 A B x f t).
Proof. exact (eq_refl (term113 A B x f t)). Qed.
Lemma lem3490307 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term222 A B s x f t) = (term116 A B s x f t).
Proof. exact (MK_COMB (@lem3490305 A B x f s) (@lem3490306 A B x f t)). Qed.
Lemma lem3490308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490309 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term227 A B s x f t) = (term228 A B s x f t).
Proof. exact (MK_COMB (@lem3490308) (@lem3490307 A B s x f t)). Qed.
Lemma lem3490310 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term184 A B x f s x') = (term110 A B x f s x').
Proof. exact (eq_refl (term184 A B x f s x')). Qed.
Lemma lem3490311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490312 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term229 A B x f s x') = (term230 A B x f s x').
Proof. exact (MK_COMB (@lem3490311) (@lem3490310 A B x f s x')). Qed.
Lemma lem3490313 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term113 A B x f t) = (term113 A B x f t).
Proof. exact (eq_refl (term113 A B x f t)). Qed.
Lemma lem3490314 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term231 A B s x x' f t) = (term232 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490312 A B x' f s x) (@lem3490313 A B x' f t)). Qed.
Lemma lem3490315 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term233 A B s x f t) = (term234 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490314 A B s x' x f t)). Qed.
Lemma lem3490316 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490317 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term223 A B s x f t) = (term235 A B s x f t).
Proof. exact (MK_COMB (@lem3490316 A) (@lem3490315 A B s x f t)). Qed.
Lemma lem3490318 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term222 A B s x f t) = (term223 A B s x f t)) = ((term116 A B s x f t) = (term235 A B s x f t)).
Proof. exact (MK_COMB (@lem3490309 A B s x f t) (@lem3490317 A B s x f t)). Qed.
Lemma lem3490319 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term116 A B s x f t) = (term235 A B s x f t).
Proof. exact (EQ_MP (@lem3490318 A B s x f t) (@lem3490299 A B s x f t)). Qed.
Lemma lem3490321 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3490322 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (@lem3490321 A P Q). Qed.
Lemma lem3490323 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term238 A B s x x' f t) = (term239 A B s x x' f t).
Proof. exact (@lem3490322 A (term110 A B x' f s x) (term112 A B x' f t)). Qed.
Lemma lem3490324 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term184 A B x f t x') = (term110 A B x f t x').
Proof. exact (eq_refl (term184 A B x f t x')). Qed.
Lemma lem3490325 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term224 A B x f t) = (term112 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490324 A B x f t x')). Qed.
Lemma lem3490326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490327 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term225 A B x f t) = (term113 A B x f t).
Proof. exact (MK_COMB (@lem3490326 A) (@lem3490325 A B x f t)). Qed.
Lemma lem3490328 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term230 A B x f s x') = (term230 A B x f s x').
Proof. exact (eq_refl (term230 A B x f s x')). Qed.
Lemma lem3490329 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term238 A B s x x' f t) = (term232 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490328 A B x' f s x) (@lem3490327 A B x' f t)). Qed.
Lemma lem3490330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490331 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term240 A B s x x' f t) = (term241 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490330) (@lem3490329 A B s x x' f t)). Qed.
Lemma lem3490332 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term184 A B x f t x') = (term110 A B x f t x').
Proof. exact (eq_refl (term184 A B x f t x')). Qed.
Lemma lem3490333 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term230 A B x f s x') = (term230 A B x f s x').
Proof. exact (eq_refl (term230 A B x f s x')). Qed.
Lemma lem3490334 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term242 A B s x x' f t x'') = (term243 A B s x x' f t x'').
Proof. exact (MK_COMB (@lem3490333 A B x' f s x) (@lem3490332 A B x' f t x'')). Qed.
Lemma lem3490335 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term244 A B s x x' f t) = (term245 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3490334 A B s x x' f t x'')). Qed.
Lemma lem3490336 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490337 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term239 A B s x x' f t) = (term246 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490336 A) (@lem3490335 A B s x x' f t)). Qed.
Lemma lem3490338 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term238 A B s x x' f t) = (term239 A B s x x' f t)) = ((term232 A B s x x' f t) = (term246 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3490331 A B s x x' f t) (@lem3490337 A B s x x' f t)). Qed.
Lemma lem3490339 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term232 A B s x x' f t) = (term246 A B s x x' f t).
Proof. exact (EQ_MP (@lem3490338 A B s x x' f t) (@lem3490323 A B s x x' f t)). Qed.
Lemma lem3490340 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term234 A B s x f t) = (term247 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490339 A B s x' x f t)). Qed.
Lemma lem3490341 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490342 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term235 A B s x f t) = (term248 A B s x f t).
Proof. exact (MK_COMB (@lem3490341 A) (@lem3490340 A B s x f t)). Qed.
Lemma lem3490343 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term116 A B s x f t) = (term248 A B s x f t).
Proof. exact (TRANS (@lem3490319 A B s x f t) (@lem3490342 A B s x f t)). Qed.
Lemma lem3490344 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term195 A B x f s t) = (term195 A B x f s t).
Proof. exact (eq_refl (term195 A B x f s t)). Qed.
Lemma lem3490345 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term197 A B s x f t) = (term249 A B s x f t).
Proof. exact (MK_COMB (@lem3490344 A B x f s t) (@lem3490343 A B s x f t)). Qed.
Lemma lem3490347 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3490348 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (@lem3490347 A P Q). Qed.
Lemma lem3490349 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term250 A B s x f t) = (term251 A B s x f t).
Proof. exact (@lem3490348 A (term179 A B x f s t) (term247 A B s x f t)). Qed.
Lemma lem3490350 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term252 A B s x' f t x) = (term246 A B s x x' f t).
Proof. exact (eq_refl (term252 A B s x' f t x)). Qed.
Lemma lem3490351 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term253 A B s x f t) = (term247 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490350 A B s x' x f t)). Qed.
Lemma lem3490352 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490353 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term254 A B s x f t) = (term248 A B s x f t).
Proof. exact (MK_COMB (@lem3490352 A) (@lem3490351 A B s x f t)). Qed.
Lemma lem3490354 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term195 A B x f s t) = (term195 A B x f s t).
Proof. exact (eq_refl (term195 A B x f s t)). Qed.
Lemma lem3490355 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term250 A B s x f t) = (term249 A B s x f t).
Proof. exact (MK_COMB (@lem3490354 A B x f s t) (@lem3490353 A B s x f t)). Qed.
Lemma lem3490356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490357 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term255 A B s x f t) = (term256 A B s x f t).
Proof. exact (MK_COMB (@lem3490356) (@lem3490355 A B s x f t)). Qed.
Lemma lem3490358 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term252 A B s x' f t x) = (term246 A B s x x' f t).
Proof. exact (eq_refl (term252 A B s x' f t x)). Qed.
Lemma lem3490359 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term195 A B x f s t) = (term195 A B x f s t).
Proof. exact (eq_refl (term195 A B x f s t)). Qed.
Lemma lem3490360 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term257 A B s x' f t x) = (term258 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490359 A B x' f s t) (@lem3490358 A B s x x' f t)). Qed.
Lemma lem3490361 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term259 A B s x f t) = (term260 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490360 A B s x' x f t)). Qed.
Lemma lem3490362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490363 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term251 A B s x f t) = (term261 A B s x f t).
Proof. exact (MK_COMB (@lem3490362 A) (@lem3490361 A B s x f t)). Qed.
Lemma lem3490364 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term250 A B s x f t) = (term251 A B s x f t)) = ((term249 A B s x f t) = (term261 A B s x f t)).
Proof. exact (MK_COMB (@lem3490357 A B s x f t) (@lem3490363 A B s x f t)). Qed.
Lemma lem3490365 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term249 A B s x f t) = (term261 A B s x f t).
Proof. exact (EQ_MP (@lem3490364 A B s x f t) (@lem3490349 A B s x f t)). Qed.
Lemma lem3490367 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3490368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (@lem3490367 A P Q). Qed.
Lemma lem3490369 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term262 A B s x x' f t) = (term263 A B s x x' f t).
Proof. exact (@lem3490368 A (term179 A B x' f s t) (term245 A B s x x' f t)). Qed.
Lemma lem3490370 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term264 A B s x x' f t x'') = (term243 A B s x x' f t x'').
Proof. exact (eq_refl (term264 A B s x x' f t x'')). Qed.
Lemma lem3490371 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term265 A B s x x' f t) = (term245 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3490370 A B s x x' f t x'')). Qed.
Lemma lem3490372 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490373 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term266 A B s x x' f t) = (term246 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490372 A) (@lem3490371 A B s x x' f t)). Qed.
Lemma lem3490374 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term195 A B x f s t) = (term195 A B x f s t).
Proof. exact (eq_refl (term195 A B x f s t)). Qed.
Lemma lem3490375 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term262 A B s x x' f t) = (term258 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490374 A B x' f s t) (@lem3490373 A B s x x' f t)). Qed.
Lemma lem3490376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490377 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term267 A B s x x' f t) = (term268 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490376) (@lem3490375 A B s x x' f t)). Qed.
Lemma lem3490378 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term264 A B s x x' f t x'') = (term243 A B s x x' f t x'').
Proof. exact (eq_refl (term264 A B s x x' f t x'')). Qed.
Lemma lem3490379 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term195 A B x f s t) = (term195 A B x f s t).
Proof. exact (eq_refl (term195 A B x f s t)). Qed.
Lemma lem3490380 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term269 A B s x x' f t x'') = (term270 A B s x x' f t x'').
Proof. exact (MK_COMB (@lem3490379 A B x' f s t) (@lem3490378 A B s x x' f t x'')). Qed.
Lemma lem3490381 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term271 A B s x x' f t) = (term272 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3490380 A B s x x' f t x'')). Qed.
Lemma lem3490382 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490383 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term263 A B s x x' f t) = (term273 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490382 A) (@lem3490381 A B s x x' f t)). Qed.
Lemma lem3490384 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term262 A B s x x' f t) = (term263 A B s x x' f t)) = ((term258 A B s x x' f t) = (term273 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3490377 A B s x x' f t) (@lem3490383 A B s x x' f t)). Qed.
Lemma lem3490385 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term258 A B s x x' f t) = (term273 A B s x x' f t).
Proof. exact (EQ_MP (@lem3490384 A B s x x' f t) (@lem3490369 A B s x x' f t)). Qed.
Lemma lem3490386 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term260 A B s x f t) = (term274 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490385 A B s x' x f t)). Qed.
Lemma lem3490387 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490388 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term261 A B s x f t) = (term275 A B s x f t).
Proof. exact (MK_COMB (@lem3490387 A) (@lem3490386 A B s x f t)). Qed.
Lemma lem3490389 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term249 A B s x f t) = (term275 A B s x f t).
Proof. exact (TRANS (@lem3490365 A B s x f t) (@lem3490388 A B s x f t)). Qed.
Lemma lem3490390 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term197 A B s x f t) = (term275 A B s x f t).
Proof. exact (TRANS (@lem3490345 A B s x f t) (@lem3490389 A B s x f t)). Qed.
Lemma lem3490391 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term204 A B s x f t) = (term276 A B s x f t).
Proof. exact (MK_COMB (@lem3490295 A B s x f t) (@lem3490390 A B s x f t)). Qed.
Lemma lem3490393 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3490394 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem3490393 A P Q). Qed.
Lemma lem3490395 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term279 A B s x f t) = (term280 A B s x f t).
Proof. exact (@lem3490394 A (term219 A B s x f t) (term274 A B s x f t)). Qed.
Lemma lem3490396 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term281 A B s x' f t x) = (term217 A B x s x' f t).
Proof. exact (eq_refl (term281 A B s x' f t x)). Qed.
Lemma lem3490397 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term282 A B s x f t) = (term219 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490396 A B x' s x f t)). Qed.
Lemma lem3490398 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490399 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term283 A B s x f t) = (term220 A B s x f t).
Proof. exact (MK_COMB (@lem3490398 A) (@lem3490397 A B s x f t)). Qed.
Lemma lem3490400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490401 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term284 A B s x f t) = (term221 A B s x f t).
Proof. exact (MK_COMB (@lem3490400) (@lem3490399 A B s x f t)). Qed.
Lemma lem3490402 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term285 A B s x' f t x) = (term273 A B s x x' f t).
Proof. exact (eq_refl (term285 A B s x' f t x)). Qed.
Lemma lem3490403 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term286 A B s x f t) = (term274 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490402 A B s x' x f t)). Qed.
Lemma lem3490404 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490405 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term287 A B s x f t) = (term275 A B s x f t).
Proof. exact (MK_COMB (@lem3490404 A) (@lem3490403 A B s x f t)). Qed.
Lemma lem3490406 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term279 A B s x f t) = (term276 A B s x f t).
Proof. exact (MK_COMB (@lem3490401 A B s x f t) (@lem3490405 A B s x f t)). Qed.
Lemma lem3490407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490408 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term288 A B s x f t) = (term289 A B s x f t).
Proof. exact (MK_COMB (@lem3490407) (@lem3490406 A B s x f t)). Qed.
Lemma lem3490409 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term281 A B s x' f t x) = (term217 A B x s x' f t).
Proof. exact (eq_refl (term281 A B s x' f t x)). Qed.
Lemma lem3490410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490411 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term290 A B s x' f t x) = (term291 A B x s x' f t).
Proof. exact (MK_COMB (@lem3490410) (@lem3490409 A B x s x' f t)). Qed.
Lemma lem3490412 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term285 A B s x' f t x) = (term273 A B s x x' f t).
Proof. exact (eq_refl (term285 A B s x' f t x)). Qed.
Lemma lem3490413 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term292 A B s x' f t x) = (term293 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490411 A B x s x' f t) (@lem3490412 A B s x x' f t)). Qed.
Lemma lem3490414 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term294 A B s x f t) = (term295 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490413 A B s x' x f t)). Qed.
Lemma lem3490415 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490416 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term280 A B s x f t) = (term296 A B s x f t).
Proof. exact (MK_COMB (@lem3490415 A) (@lem3490414 A B s x f t)). Qed.
Lemma lem3490417 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term279 A B s x f t) = (term280 A B s x f t)) = ((term276 A B s x f t) = (term296 A B s x f t)).
Proof. exact (MK_COMB (@lem3490408 A B s x f t) (@lem3490416 A B s x f t)). Qed.
Lemma lem3490418 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term276 A B s x f t) = (term296 A B s x f t).
Proof. exact (EQ_MP (@lem3490417 A B s x f t) (@lem3490395 A B s x f t)). Qed.
Lemma lem3490420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3490421 {A : Type'} (P : Prop) (Q : A -> Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem3490420 A P Q). Qed.
Lemma lem3490422 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term299 A B s x x' f t) = (term300 A B s x x' f t).
Proof. exact (@lem3490421 A (term217 A B x s x' f t) (term272 A B s x x' f t)). Qed.
Lemma lem3490423 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term301 A B s x x' f t x'') = (term270 A B s x x' f t x'').
Proof. exact (eq_refl (term301 A B s x x' f t x'')). Qed.
Lemma lem3490424 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term302 A B s x x' f t) = (term272 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3490423 A B s x x' f t x'')). Qed.
Lemma lem3490425 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490426 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term303 A B s x x' f t) = (term273 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490425 A) (@lem3490424 A B s x x' f t)). Qed.
Lemma lem3490427 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term291 A B x s x' f t) = (term291 A B x s x' f t).
Proof. exact (eq_refl (term291 A B x s x' f t)). Qed.
Lemma lem3490428 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term299 A B s x x' f t) = (term293 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490427 A B x s x' f t) (@lem3490426 A B s x x' f t)). Qed.
Lemma lem3490429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3490430 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term304 A B s x x' f t) = (term305 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490429) (@lem3490428 A B s x x' f t)). Qed.
Lemma lem3490431 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term301 A B s x x' f t x'') = (term270 A B s x x' f t x'').
Proof. exact (eq_refl (term301 A B s x x' f t x'')). Qed.
Lemma lem3490432 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term291 A B x s x' f t) = (term291 A B x s x' f t).
Proof. exact (eq_refl (term291 A B x s x' f t)). Qed.
Lemma lem3490433 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term306 A B s x x' f t x'') = (term307 A B s x x' f t x'').
Proof. exact (MK_COMB (@lem3490432 A B x s x' f t) (@lem3490431 A B s x x' f t x'')). Qed.
Lemma lem3490434 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term308 A B s x x' f t) = (term309 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3490433 A B s x x' f t x'')). Qed.
Lemma lem3490435 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490436 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term300 A B s x x' f t) = (term310 A B s x x' f t).
Proof. exact (MK_COMB (@lem3490435 A) (@lem3490434 A B s x x' f t)). Qed.
Lemma lem3490437 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term299 A B s x x' f t) = (term300 A B s x x' f t)) = ((term293 A B s x x' f t) = (term310 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3490430 A B s x x' f t) (@lem3490436 A B s x x' f t)). Qed.
Lemma lem3490438 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term293 A B s x x' f t) = (term310 A B s x x' f t).
Proof. exact (EQ_MP (@lem3490437 A B s x x' f t) (@lem3490422 A B s x x' f t)). Qed.
Lemma lem3490439 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term295 A B s x f t) = (term311 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490438 A B s x' x f t)). Qed.
Lemma lem3490440 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3490441 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term296 A B s x f t) = (term312 A B s x f t).
Proof. exact (MK_COMB (@lem3490440 A) (@lem3490439 A B s x f t)). Qed.
Lemma lem3490442 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term276 A B s x f t) = (term312 A B s x f t).
Proof. exact (TRANS (@lem3490418 A B s x f t) (@lem3490441 A B s x f t)). Qed.
Lemma lem3490444 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term204 A B s x f t) = (term312 A B s x f t).
Proof. exact (TRANS (@lem3490391 A B s x f t) (@lem3490442 A B s x f t)). Qed.
Lemma lem3490445 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term138 A B s x f t) = (term312 A B s x f t).
Proof. exact (TRANS (@lem3490012 A B s x f t) (@lem3490444 A B s x f t)). Qed.
Lemma lem3490446 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term138 A B s x f t) : term312 A B s x f t.
Proof. exact (EQ_MP (@lem3490445 A B s x f t) (@lem3489586 A B s x f t h1)). Qed.
Lemma lem3490447 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term310 A B s x' x f t) : term310 A B s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3490448 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term307 A B s x' x f t x'') : term307 A B s x' x f t x''.
Proof. exact (h1). Qed.
Lemma lem3490459 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term160 A s u x) = (term160 A s u x).
Proof. exact (eq_refl (term160 A s u x)). Qed.
Lemma lem3490460 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term161 A s u) = (term161 A s u).
Proof. exact (fun_ext (fun x : A => @lem3490459 A s u x)). Qed.
Lemma lem3490461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490462 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term162 A s u) = (term162 A s u).
Proof. exact (MK_COMB (@lem3490461 A) (@lem3490460 A s u)). Qed.
Lemma lem3490465 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3490484 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term140 A B x f t x') = (term140 A B x f t x').
Proof. exact (eq_refl (term140 A B x f t x')). Qed.
Lemma lem3490485 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term148 A B x f t) = (term148 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490484 A B x f t x')). Qed.
Lemma lem3490486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490487 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term149 A B x f t) = (term149 A B x f t).
Proof. exact (MK_COMB (@lem3490486 A) (@lem3490485 A B x f t)). Qed.
Lemma lem3490494 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3490495 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term152 A B u x f t) = (term152 A B u x f t).
Proof. exact (MK_COMB (@lem3490494 A u x) (@lem3490487 A B x f t)). Qed.
Lemma lem3490496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490497 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term155 A B u x f t) = (term155 A B u x f t).
Proof. exact (MK_COMB (@lem3490496) (@lem3490495 A B u x f t)). Qed.
Lemma lem3490498 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term157 A B u f t x) = (term157 A B u f t x).
Proof. exact (MK_COMB (@lem3490497 A B u x f t) (@lem3490465 A t x)). Qed.
Lemma lem3490499 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term158 A B u f t) = (term158 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem3490498 A B u f t x)). Qed.
Lemma lem3490500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490501 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term159 A B u f t) = (term159 A B u f t).
Proof. exact (MK_COMB (@lem3490500 A) (@lem3490499 A B u f t)). Qed.
Lemma lem3490502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490503 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term163 A B u f t) = (term163 A B u f t).
Proof. exact (MK_COMB (@lem3490502) (@lem3490501 A B u f t)). Qed.
Lemma lem3490504 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term164 A B f t s u) = (term164 A B f t s u).
Proof. exact (MK_COMB (@lem3490503 A B u f t) (@lem3490462 A s u)). Qed.
Lemma lem3490515 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term160 A t u x) = (term160 A t u x).
Proof. exact (eq_refl (term160 A t u x)). Qed.
Lemma lem3490516 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term161 A t u) = (term161 A t u).
Proof. exact (fun_ext (fun x : A => @lem3490515 A t u x)). Qed.
Lemma lem3490517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490518 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term162 A t u) = (term162 A t u).
Proof. exact (MK_COMB (@lem3490517 A) (@lem3490516 A t u)). Qed.
Lemma lem3490521 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3490540 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term140 A B x f s x') = (term140 A B x f s x').
Proof. exact (eq_refl (term140 A B x f s x')). Qed.
Lemma lem3490541 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term148 A B x f s) = (term148 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3490540 A B x f s x')). Qed.
Lemma lem3490542 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490543 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term149 A B x f s).
Proof. exact (MK_COMB (@lem3490542 A) (@lem3490541 A B x f s)). Qed.
Lemma lem3490550 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3490551 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term152 A B u x f s) = (term152 A B u x f s).
Proof. exact (MK_COMB (@lem3490550 A u x) (@lem3490543 A B x f s)). Qed.
Lemma lem3490552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490553 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term155 A B u x f s) = (term155 A B u x f s).
Proof. exact (MK_COMB (@lem3490552) (@lem3490551 A B u x f s)). Qed.
Lemma lem3490554 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term157 A B u f s x) = (term157 A B u f s x).
Proof. exact (MK_COMB (@lem3490553 A B u x f s) (@lem3490521 A s x)). Qed.
Lemma lem3490555 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term158 A B u f s) = (term158 A B u f s).
Proof. exact (fun_ext (fun x : A => @lem3490554 A B u f s x)). Qed.
Lemma lem3490556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490557 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term159 A B u f s) = (term159 A B u f s).
Proof. exact (MK_COMB (@lem3490556 A) (@lem3490555 A B u f s)). Qed.
Lemma lem3490558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490559 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term163 A B u f s) = (term163 A B u f s).
Proof. exact (MK_COMB (@lem3490558) (@lem3490557 A B u f s)). Qed.
Lemma lem3490560 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term164 A B f s t u) = (term164 A B f s t u).
Proof. exact (MK_COMB (@lem3490559 A B u f s) (@lem3490518 A t u)). Qed.
Lemma lem3490561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490562 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term165 A B f s t u) = (term165 A B f s t u).
Proof. exact (MK_COMB (@lem3490561) (@lem3490560 A B f s t u)). Qed.
Lemma lem3490563 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term166 A B f t s u) = (term166 A B f t s u).
Proof. exact (MK_COMB (@lem3490562 A B f s t u) (@lem3490504 A B f t s u)). Qed.
Lemma lem3490564 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term92 A B f t s u) : term166 A B f t s u.
Proof. exact (EQ_MP (@lem3490563 A B f t s u) (@lem3489908 A B f t s u h1)). Qed.
Lemma lem3490593 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term243 A B s x' x f t x'') = (term243 A B s x' x f t x'').
Proof. exact (eq_refl (term243 A B s x' x f t x'')). Qed.
Lemma lem3490618 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term171 A B x f s t x') = (term171 A B x f s t x').
Proof. exact (eq_refl (term171 A B x f s t x')). Qed.
Lemma lem3490619 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term178 A B x f s t) = (term178 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3490618 A B x f s t x')). Qed.
Lemma lem3490620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490621 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term179 A B x f s t) = (term179 A B x f s t).
Proof. exact (MK_COMB (@lem3490620 A) (@lem3490619 A B x f s t)). Qed.
Lemma lem3490622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3490623 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term195 A B x f s t) = (term195 A B x f s t).
Proof. exact (MK_COMB (@lem3490622) (@lem3490621 A B x f s t)). Qed.
Lemma lem3490624 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term270 A B s x' x f t x'') = (term270 A B s x' x f t x'').
Proof. exact (MK_COMB (@lem3490623 A B x f s t) (@lem3490593 A B s x' x f t x'')). Qed.
Lemma lem3490641 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term181 A B x f t x') = (term181 A B x f t x').
Proof. exact (eq_refl (term181 A B x f t x')). Qed.
Lemma lem3490642 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term187 A B x f t) = (term187 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490641 A B x f t x')). Qed.
Lemma lem3490643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490644 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term188 A B x f t) = (term188 A B x f t).
Proof. exact (MK_COMB (@lem3490643 A) (@lem3490642 A B x f t)). Qed.
Lemma lem3490661 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term181 A B x f s x').
Proof. exact (eq_refl (term181 A B x f s x')). Qed.
Lemma lem3490662 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term187 A B x f s) = (term187 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3490661 A B x f s x')). Qed.
Lemma lem3490663 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490664 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term188 A B x f s) = (term188 A B x f s).
Proof. exact (MK_COMB (@lem3490663 A) (@lem3490662 A B x f s)). Qed.
Lemma lem3490665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490666 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term190 A B x f s) = (term190 A B x f s).
Proof. exact (MK_COMB (@lem3490665) (@lem3490664 A B x f s)). Qed.
Lemma lem3490667 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term192 A B s x f t) = (term192 A B s x f t).
Proof. exact (MK_COMB (@lem3490666 A B x f s) (@lem3490644 A B x f t)). Qed.
Lemma lem3490688 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term215 A B x f s t x') = (term215 A B x f s t x').
Proof. exact (eq_refl (term215 A B x f s t x')). Qed.
Lemma lem3490689 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term217 A B x' s x f t) = (term217 A B x' s x f t).
Proof. exact (MK_COMB (@lem3490688 A B x f s t x') (@lem3490667 A B s x f t)). Qed.
Lemma lem3490690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3490691 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term291 A B x' s x f t) = (term291 A B x' s x f t).
Proof. exact (MK_COMB (@lem3490690) (@lem3490689 A B x' s x f t)). Qed.
Lemma lem3490692 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term307 A B s x' x f t x'') = (term307 A B s x' x f t x'').
Proof. exact (MK_COMB (@lem3490691 A B x' s x f t) (@lem3490624 A B s x' x f t x'')). Qed.
Lemma lem3490693 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term307 A B s x' x f t x'') : term307 A B s x' x f t x''.
Proof. exact (EQ_MP (@lem3490692 A B s x' x f t x'') (@lem3490448 A B s x' x f t x'' h1)). Qed.
Lemma lem3490694 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term217 A B x' s x f t.
Proof. exact (h1). Qed.
Lemma lem3490695 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term270 A B s x' x f t x''.
Proof. exact (h1). Qed.
Lemma lem3490696 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term192 A B s x f t.
Proof. exact (proj2 (@lem3490694 A B x' s x f t h1)). Qed.
Lemma lem3490697 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term101 A B x f s t x'.
Proof. exact (proj1 (@lem3490694 A B x' s x f t h1)). Qed.
Lemma lem3490698 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term98 A s t x'.
Proof. exact (proj2 (@lem3490697 A B x' s x f t h1)). Qed.
Lemma lem3490702 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term188 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3490703 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term188 A B x f t.
Proof. exact (h1). Qed.
Lemma lem3490716 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term243 A B s x' x f t x''.
Proof. exact (proj2 (@lem3490695 A B s x' x f t x'' h1)). Qed.
Lemma lem3490717 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term179 A B x f s t.
Proof. exact (proj1 (@lem3490695 A B s x' x f t x'' h1)). Qed.
Lemma lem3490718 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term110 A B x f t x''.
Proof. exact (proj2 (@lem3490716 A B s x' x f t x'' h1)). Qed.
Lemma lem3490719 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term110 A B x f s x'.
Proof. exact (proj1 (@lem3490716 A B s x' x f t x'' h1)). Qed.
Lemma lem3490724 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term164 A B f s t u.
Proof. exact (h1). Qed.
Lemma lem3490725 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term164 A B f t s u.
Proof. exact (h1). Qed.
Lemma lem3490726 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term162 A t u.
Proof. exact (proj2 (@lem3490724 A B f s t u h1)). Qed.
Lemma lem3490727 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term159 A B u f s.
Proof. exact (proj1 (@lem3490724 A B f s t u h1)). Qed.
Lemma lem3490728 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term162 A s u.
Proof. exact (proj2 (@lem3490725 A B f t s u h1)). Qed.
Lemma lem3490729 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term159 A B u f t.
Proof. exact (proj1 (@lem3490725 A B f t s u h1)). Qed.
Lemma lem3490749 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term181 A B x f s x').
Proof. exact (eq_refl (term181 A B x f s x')). Qed.
Lemma lem3490750 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term187 A B x f s) = (term187 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3490749 A B x f s x')). Qed.
Lemma lem3490751 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490753 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term188 A B x f s) = (term188 A B x f s).
Proof. exact (MK_COMB (@lem3490751 A) (@lem3490750 A B x f s)). Qed.
Lemma lem3490754 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term188 A B x f s.
Proof. exact (EQ_MP (@lem3490753 A B x f s) (@lem3490702 A B x f s h1)). Qed.
Lemma lem3490866 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term181 A B x f s x').
Proof. exact (eq_refl (term181 A B x f s x')). Qed.
Lemma lem3490867 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term187 A B x f s) = (term187 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3490866 A B x f s x')). Qed.
Lemma lem3490868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490870 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term188 A B x f s) = (term188 A B x f s).
Proof. exact (MK_COMB (@lem3490868 A) (@lem3490867 A B x f s)). Qed.
Lemma lem3490871 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term188 A B x f s.
Proof. exact (EQ_MP (@lem3490870 A B x f s) (@lem3490702 A B x f s h1)). Qed.
Lemma lem3490983 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term181 A B x f t x') = (term181 A B x f t x').
Proof. exact (eq_refl (term181 A B x f t x')). Qed.
Lemma lem3490984 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term187 A B x f t) = (term187 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3490983 A B x f t x')). Qed.
Lemma lem3490985 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3490987 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term188 A B x f t) = (term188 A B x f t).
Proof. exact (MK_COMB (@lem3490985 A) (@lem3490984 A B x f t)). Qed.
Lemma lem3490988 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term188 A B x f t.
Proof. exact (EQ_MP (@lem3490987 A B x f t) (@lem3490703 A B x f t h1)). Qed.
Lemma lem3491100 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term181 A B x f t x') = (term181 A B x f t x').
Proof. exact (eq_refl (term181 A B x f t x')). Qed.
Lemma lem3491101 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term187 A B x f t) = (term187 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3491100 A B x f t x')). Qed.
Lemma lem3491102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491104 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term188 A B x f t) = (term188 A B x f t).
Proof. exact (MK_COMB (@lem3491102 A) (@lem3491101 A B x f t)). Qed.
Lemma lem3491105 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term188 A B x f t.
Proof. exact (EQ_MP (@lem3491104 A B x f t) (@lem3490703 A B x f t h1)). Qed.
Lemma lem3491211 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term171 A B x f s t x') = (term171 A B x f s t x').
Proof. exact (eq_refl (term171 A B x f s t x')). Qed.
Lemma lem3491212 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term178 A B x f s t) = (term178 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3491211 A B x f s t x')). Qed.
Lemma lem3491213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491215 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term179 A B x f s t) = (term179 A B x f s t).
Proof. exact (MK_COMB (@lem3491213 A) (@lem3491212 A B x f s t)). Qed.
Lemma lem3491216 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term179 A B x f s t.
Proof. exact (EQ_MP (@lem3491215 A B x f s t) (@lem3490717 A B s x' x f t x'' h1)). Qed.
Lemma lem3491234 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3491235 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem3491234 A P Q). Qed.
Lemma lem3491236 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term315 A B u x f s) = (term316 A B u x f s).
Proof. exact (@lem3491235 A (term317 A u x) (term148 A B x f s)). Qed.
Lemma lem3491237 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term318 A B x f s x') = (term140 A B x f s x').
Proof. exact (eq_refl (term318 A B x f s x')). Qed.
Lemma lem3491238 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term319 A B x f s) = (term148 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3491237 A B x f s x')). Qed.
Lemma lem3491239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491240 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term320 A B x f s) = (term149 A B x f s).
Proof. exact (MK_COMB (@lem3491239 A) (@lem3491238 A B x f s)). Qed.
Lemma lem3491241 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3491242 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term315 A B u x f s) = (term152 A B u x f s).
Proof. exact (MK_COMB (@lem3491241 A u x) (@lem3491240 A B x f s)). Qed.
Lemma lem3491243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491244 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term321 A B u x f s) = (term322 A B u x f s).
Proof. exact (MK_COMB (@lem3491243) (@lem3491242 A B u x f s)). Qed.
Lemma lem3491245 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term318 A B x f s x') = (term140 A B x f s x').
Proof. exact (eq_refl (term318 A B x f s x')). Qed.
Lemma lem3491246 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3491247 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term323 A B u x f s x') = (term324 A B u x f s x').
Proof. exact (MK_COMB (@lem3491246 A u x) (@lem3491245 A B x f s x')). Qed.
Lemma lem3491248 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term325 A B u x f s) = (term326 A B u x f s).
Proof. exact (fun_ext (fun x' : A => @lem3491247 A B u x f s x')). Qed.
Lemma lem3491249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491250 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term316 A B u x f s) = (term327 A B u x f s).
Proof. exact (MK_COMB (@lem3491249 A) (@lem3491248 A B u x f s)). Qed.
Lemma lem3491251 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : ((term315 A B u x f s) = (term316 A B u x f s)) = ((term152 A B u x f s) = (term327 A B u x f s)).
Proof. exact (MK_COMB (@lem3491244 A B u x f s) (@lem3491250 A B u x f s)). Qed.
Lemma lem3491252 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term152 A B u x f s) = (term327 A B u x f s).
Proof. exact (EQ_MP (@lem3491251 A B u x f s) (@lem3491236 A B u x f s)). Qed.
Lemma lem3491253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3491254 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term155 A B u x f s) = (term328 A B u x f s).
Proof. exact (MK_COMB (@lem3491253) (@lem3491252 A B u x f s)). Qed.
Lemma lem3491255 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3491256 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term157 A B u f s x) = (term329 A B u f s x).
Proof. exact (MK_COMB (@lem3491254 A B u x f s) (@lem3491255 A s x)). Qed.
Lemma lem3491258 {A : Type'} (P : A -> Prop) (Q : Prop) : (term330 A P Q) = (term331 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3491259 {A : Type'} (P : A -> Prop) (Q : Prop) : (term330 A P Q) = (term331 A P Q).
Proof. exact (@lem3491258 A P Q). Qed.
Lemma lem3491260 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term332 A B u f s x) = (term333 A B u f s x).
Proof. exact (@lem3491259 A (term326 A B u x f s) (s x)). Qed.
Lemma lem3491261 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term334 A B u x f s x') = (term324 A B u x f s x').
Proof. exact (eq_refl (term334 A B u x f s x')). Qed.
Lemma lem3491262 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term335 A B u x f s) = (term326 A B u x f s).
Proof. exact (fun_ext (fun x' : A => @lem3491261 A B u x f s x')). Qed.
Lemma lem3491263 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491264 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term336 A B u x f s) = (term327 A B u x f s).
Proof. exact (MK_COMB (@lem3491263 A) (@lem3491262 A B u x f s)). Qed.
Lemma lem3491265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3491266 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) : (term337 A B u x f s) = (term328 A B u x f s).
Proof. exact (MK_COMB (@lem3491265) (@lem3491264 A B u x f s)). Qed.
Lemma lem3491267 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3491268 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term332 A B u f s x) = (term329 A B u f s x).
Proof. exact (MK_COMB (@lem3491266 A B u x f s) (@lem3491267 A s x)). Qed.
Lemma lem3491269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491270 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term338 A B u f s x) = (term339 A B u f s x).
Proof. exact (MK_COMB (@lem3491269) (@lem3491268 A B u f s x)). Qed.
Lemma lem3491271 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term334 A B u x f s x') = (term324 A B u x f s x').
Proof. exact (eq_refl (term334 A B u x f s x')). Qed.
Lemma lem3491272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3491273 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term340 A B u x f s x') = (term341 A B u x f s x').
Proof. exact (MK_COMB (@lem3491272) (@lem3491271 A B u x f s x')). Qed.
Lemma lem3491274 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3491275 {A B : Type'} (u : A -> Prop) (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term342 A B u f x' s x) = (term343 A B u f x' s x).
Proof. exact (MK_COMB (@lem3491273 A B u x f s x') (@lem3491274 A s x)). Qed.
Lemma lem3491276 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term344 A B u f s x) = (term345 A B u f s x).
Proof. exact (fun_ext (fun x' : A => @lem3491275 A B u f x' s x)). Qed.
Lemma lem3491277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491278 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term333 A B u f s x) = (term346 A B u f s x).
Proof. exact (MK_COMB (@lem3491277 A) (@lem3491276 A B u f s x)). Qed.
Lemma lem3491279 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : ((term332 A B u f s x) = (term333 A B u f s x)) = ((term329 A B u f s x) = (term346 A B u f s x)).
Proof. exact (MK_COMB (@lem3491270 A B u f s x) (@lem3491278 A B u f s x)). Qed.
Lemma lem3491280 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term329 A B u f s x) = (term346 A B u f s x).
Proof. exact (EQ_MP (@lem3491279 A B u f s x) (@lem3491260 A B u f s x)). Qed.
Lemma lem3491281 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term157 A B u f s x) = (term346 A B u f s x).
Proof. exact (TRANS (@lem3491256 A B u f s x) (@lem3491280 A B u f s x)). Qed.
Lemma lem3491282 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term158 A B u f s) = (term347 A B u f s).
Proof. exact (fun_ext (fun x : A => @lem3491281 A B u f s x)). Qed.
Lemma lem3491283 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491284 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term159 A B u f s) = (term348 A B u f s).
Proof. exact (MK_COMB (@lem3491283 A) (@lem3491282 A B u f s)). Qed.
Lemma lem3491303 {A B : Type'} (u : A -> Prop) (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term343 A B u f x' s x) = (term343 A B u f x' s x).
Proof. exact (eq_refl (term343 A B u f x' s x)). Qed.
Lemma lem3491304 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term345 A B u f s x) = (term345 A B u f s x).
Proof. exact (fun_ext (fun x' : A => @lem3491303 A B u f x' s x)). Qed.
Lemma lem3491305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491306 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : (term346 A B u f s x) = (term346 A B u f s x).
Proof. exact (MK_COMB (@lem3491305 A) (@lem3491304 A B u f s x)). Qed.
Lemma lem3491307 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term347 A B u f s) = (term347 A B u f s).
Proof. exact (fun_ext (fun x : A => @lem3491306 A B u f s x)). Qed.
Lemma lem3491308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491309 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term348 A B u f s) = (term348 A B u f s).
Proof. exact (MK_COMB (@lem3491308 A) (@lem3491307 A B u f s)). Qed.
Lemma lem3491310 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term159 A B u f s) = (term348 A B u f s).
Proof. exact (TRANS (@lem3491284 A B u f s) (@lem3491309 A B u f s)). Qed.
Lemma lem3491311 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term348 A B u f s.
Proof. exact (EQ_MP (@lem3491310 A B u f s) (@lem3490727 A B f s t u h1)). Qed.
Lemma lem3491319 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term160 A t u x) = (term160 A t u x).
Proof. exact (eq_refl (term160 A t u x)). Qed.
Lemma lem3491320 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term161 A t u) = (term161 A t u).
Proof. exact (fun_ext (fun x : A => @lem3491319 A t u x)). Qed.
Lemma lem3491321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491323 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term162 A t u) = (term162 A t u).
Proof. exact (MK_COMB (@lem3491321 A) (@lem3491320 A t u)). Qed.
Lemma lem3491324 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term162 A t u.
Proof. exact (EQ_MP (@lem3491323 A t u) (@lem3490726 A B f s t u h1)). Qed.
Lemma lem3491338 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term171 A B x f s t x') = (term171 A B x f s t x').
Proof. exact (eq_refl (term171 A B x f s t x')). Qed.
Lemma lem3491339 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term178 A B x f s t) = (term178 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3491338 A B x f s t x')). Qed.
Lemma lem3491340 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491342 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term179 A B x f s t) = (term179 A B x f s t).
Proof. exact (MK_COMB (@lem3491340 A) (@lem3491339 A B x f s t)). Qed.
Lemma lem3491343 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term179 A B x f s t.
Proof. exact (EQ_MP (@lem3491342 A B x f s t) (@lem3490717 A B s x' x f t x'' h1)). Qed.
Lemma lem3491361 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3491362 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem3491361 A P Q). Qed.
Lemma lem3491363 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term315 A B u x f t) = (term316 A B u x f t).
Proof. exact (@lem3491362 A (term317 A u x) (term148 A B x f t)). Qed.
Lemma lem3491364 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term318 A B x f t x') = (term140 A B x f t x').
Proof. exact (eq_refl (term318 A B x f t x')). Qed.
Lemma lem3491365 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term319 A B x f t) = (term148 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3491364 A B x f t x')). Qed.
Lemma lem3491366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491367 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term320 A B x f t) = (term149 A B x f t).
Proof. exact (MK_COMB (@lem3491366 A) (@lem3491365 A B x f t)). Qed.
Lemma lem3491368 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3491369 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term315 A B u x f t) = (term152 A B u x f t).
Proof. exact (MK_COMB (@lem3491368 A u x) (@lem3491367 A B x f t)). Qed.
Lemma lem3491370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491371 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term321 A B u x f t) = (term322 A B u x f t).
Proof. exact (MK_COMB (@lem3491370) (@lem3491369 A B u x f t)). Qed.
Lemma lem3491372 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term318 A B x f t x') = (term140 A B x f t x').
Proof. exact (eq_refl (term318 A B x f t x')). Qed.
Lemma lem3491373 {A : Type'} (u : A -> Prop) (x : A) : (term150 A u x) = (term150 A u x).
Proof. exact (eq_refl (term150 A u x)). Qed.
Lemma lem3491374 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term323 A B u x f t x') = (term324 A B u x f t x').
Proof. exact (MK_COMB (@lem3491373 A u x) (@lem3491372 A B x f t x')). Qed.
Lemma lem3491375 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term325 A B u x f t) = (term326 A B u x f t).
Proof. exact (fun_ext (fun x' : A => @lem3491374 A B u x f t x')). Qed.
Lemma lem3491376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491377 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term316 A B u x f t) = (term327 A B u x f t).
Proof. exact (MK_COMB (@lem3491376 A) (@lem3491375 A B u x f t)). Qed.
Lemma lem3491378 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : ((term315 A B u x f t) = (term316 A B u x f t)) = ((term152 A B u x f t) = (term327 A B u x f t)).
Proof. exact (MK_COMB (@lem3491371 A B u x f t) (@lem3491377 A B u x f t)). Qed.
Lemma lem3491379 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term152 A B u x f t) = (term327 A B u x f t).
Proof. exact (EQ_MP (@lem3491378 A B u x f t) (@lem3491363 A B u x f t)). Qed.
Lemma lem3491380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3491381 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term155 A B u x f t) = (term328 A B u x f t).
Proof. exact (MK_COMB (@lem3491380) (@lem3491379 A B u x f t)). Qed.
Lemma lem3491382 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3491383 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term157 A B u f t x) = (term329 A B u f t x).
Proof. exact (MK_COMB (@lem3491381 A B u x f t) (@lem3491382 A t x)). Qed.
Lemma lem3491385 {A : Type'} (P : A -> Prop) (Q : Prop) : (term330 A P Q) = (term331 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3491386 {A : Type'} (P : A -> Prop) (Q : Prop) : (term330 A P Q) = (term331 A P Q).
Proof. exact (@lem3491385 A P Q). Qed.
Lemma lem3491387 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term332 A B u f t x) = (term333 A B u f t x).
Proof. exact (@lem3491386 A (term326 A B u x f t) (t x)). Qed.
Lemma lem3491388 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term334 A B u x f t x') = (term324 A B u x f t x').
Proof. exact (eq_refl (term334 A B u x f t x')). Qed.
Lemma lem3491389 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term335 A B u x f t) = (term326 A B u x f t).
Proof. exact (fun_ext (fun x' : A => @lem3491388 A B u x f t x')). Qed.
Lemma lem3491390 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491391 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term336 A B u x f t) = (term327 A B u x f t).
Proof. exact (MK_COMB (@lem3491390 A) (@lem3491389 A B u x f t)). Qed.
Lemma lem3491392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3491393 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) : (term337 A B u x f t) = (term328 A B u x f t).
Proof. exact (MK_COMB (@lem3491392) (@lem3491391 A B u x f t)). Qed.
Lemma lem3491394 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3491395 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term332 A B u f t x) = (term329 A B u f t x).
Proof. exact (MK_COMB (@lem3491393 A B u x f t) (@lem3491394 A t x)). Qed.
Lemma lem3491396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491397 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term338 A B u f t x) = (term339 A B u f t x).
Proof. exact (MK_COMB (@lem3491396) (@lem3491395 A B u f t x)). Qed.
Lemma lem3491398 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term334 A B u x f t x') = (term324 A B u x f t x').
Proof. exact (eq_refl (term334 A B u x f t x')). Qed.
Lemma lem3491399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3491400 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term340 A B u x f t x') = (term341 A B u x f t x').
Proof. exact (MK_COMB (@lem3491399) (@lem3491398 A B u x f t x')). Qed.
Lemma lem3491401 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3491402 {A B : Type'} (u : A -> Prop) (f : A -> B) (x' : A) (t : A -> Prop) (x : A) : (term342 A B u f x' t x) = (term343 A B u f x' t x).
Proof. exact (MK_COMB (@lem3491400 A B u x f t x') (@lem3491401 A t x)). Qed.
Lemma lem3491403 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term344 A B u f t x) = (term345 A B u f t x).
Proof. exact (fun_ext (fun x' : A => @lem3491402 A B u f x' t x)). Qed.
Lemma lem3491404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491405 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term333 A B u f t x) = (term346 A B u f t x).
Proof. exact (MK_COMB (@lem3491404 A) (@lem3491403 A B u f t x)). Qed.
Lemma lem3491406 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : ((term332 A B u f t x) = (term333 A B u f t x)) = ((term329 A B u f t x) = (term346 A B u f t x)).
Proof. exact (MK_COMB (@lem3491397 A B u f t x) (@lem3491405 A B u f t x)). Qed.
Lemma lem3491407 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term329 A B u f t x) = (term346 A B u f t x).
Proof. exact (EQ_MP (@lem3491406 A B u f t x) (@lem3491387 A B u f t x)). Qed.
Lemma lem3491408 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term157 A B u f t x) = (term346 A B u f t x).
Proof. exact (TRANS (@lem3491383 A B u f t x) (@lem3491407 A B u f t x)). Qed.
Lemma lem3491409 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term158 A B u f t) = (term347 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem3491408 A B u f t x)). Qed.
Lemma lem3491410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491411 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term159 A B u f t) = (term348 A B u f t).
Proof. exact (MK_COMB (@lem3491410 A) (@lem3491409 A B u f t)). Qed.
Lemma lem3491430 {A B : Type'} (u : A -> Prop) (f : A -> B) (x' : A) (t : A -> Prop) (x : A) : (term343 A B u f x' t x) = (term343 A B u f x' t x).
Proof. exact (eq_refl (term343 A B u f x' t x)). Qed.
Lemma lem3491431 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term345 A B u f t x) = (term345 A B u f t x).
Proof. exact (fun_ext (fun x' : A => @lem3491430 A B u f x' t x)). Qed.
Lemma lem3491432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491433 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) : (term346 A B u f t x) = (term346 A B u f t x).
Proof. exact (MK_COMB (@lem3491432 A) (@lem3491431 A B u f t x)). Qed.
Lemma lem3491434 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term347 A B u f t) = (term347 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem3491433 A B u f t x)). Qed.
Lemma lem3491435 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491436 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term348 A B u f t) = (term348 A B u f t).
Proof. exact (MK_COMB (@lem3491435 A) (@lem3491434 A B u f t)). Qed.
Lemma lem3491437 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term159 A B u f t) = (term348 A B u f t).
Proof. exact (TRANS (@lem3491411 A B u f t) (@lem3491436 A B u f t)). Qed.
Lemma lem3491438 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term348 A B u f t.
Proof. exact (EQ_MP (@lem3491437 A B u f t) (@lem3490729 A B f t s u h1)). Qed.
Lemma lem3491446 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term160 A s u x) = (term160 A s u x).
Proof. exact (eq_refl (term160 A s u x)). Qed.
Lemma lem3491447 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term161 A s u) = (term161 A s u).
Proof. exact (fun_ext (fun x : A => @lem3491446 A s u x)). Qed.
Lemma lem3491448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3491450 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term162 A s u) = (term162 A s u).
Proof. exact (MK_COMB (@lem3491448 A) (@lem3491447 A s u)). Qed.
Lemma lem3491451 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term162 A s u.
Proof. exact (EQ_MP (@lem3491450 A s u) (@lem3490728 A B f t s u h1)). Qed.
Lemma lem3491452 {A B : Type'} (_36773 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term349 A B x f s _36773.
Proof. exact (@lem3490754 A B x f s h1 _36773). Qed.
Lemma lem3491453 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term349 A B x f s _36773) = (term181 A B x f s _36773).
Proof. exact (eq_refl (term349 A B x f s _36773)). Qed.
Lemma lem3491464 {A B : Type'} (_36777 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term349 A B x f s _36777.
Proof. exact (@lem3490871 A B x f s h1 _36777). Qed.
Lemma lem3491465 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term349 A B x f s _36777) = (term181 A B x f s _36777).
Proof. exact (eq_refl (term349 A B x f s _36777)). Qed.
Lemma lem3491476 {A B : Type'} (_36781 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term349 A B x f t _36781.
Proof. exact (@lem3490988 A B x f t h1 _36781). Qed.
Lemma lem3491477 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term349 A B x f t _36781) = (term181 A B x f t _36781).
Proof. exact (eq_refl (term349 A B x f t _36781)). Qed.
Lemma lem3491488 {A B : Type'} (_36785 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term349 A B x f t _36785.
Proof. exact (@lem3491105 A B x f t h1 _36785). Qed.
Lemma lem3491489 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term349 A B x f t _36785) = (term181 A B x f t _36785).
Proof. exact (eq_refl (term349 A B x f t _36785)). Qed.
Lemma lem3491500 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term350 A B x f s t _36789.
Proof. exact (@lem3491216 A B s x' x f t x'' h1 _36789). Qed.
Lemma lem3491501 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term350 A B x f s t _36789) = (term171 A B x f s t _36789).
Proof. exact (eq_refl (term350 A B x f s t _36789)). Qed.
Lemma lem3491503 {A B : Type'} (_36790 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term351 A B u f s _36790.
Proof. exact (@lem3491311 A B f s t u h1 _36790). Qed.
Lemma lem3491504 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (_36790 : A) : (term351 A B u f s _36790) = (term346 A B u f s _36790).
Proof. exact (eq_refl (term351 A B u f s _36790)). Qed.
Lemma lem3491505 {A B : Type'} (_36790 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term346 A B u f s _36790.
Proof. exact (EQ_MP (@lem3491504 A B u f s _36790) (@lem3491503 A B _36790 f s t u h1)). Qed.
Lemma lem3491506 {A B : Type'} (_36790 : A) (_36791 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term352 A B u f s _36790 _36791.
Proof. exact (@lem3491505 A B _36790 f s t u h1 _36791). Qed.
Lemma lem3491507 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term352 A B u f s _36790 _36791) = (term343 A B u f _36791 s _36790).
Proof. exact (eq_refl (term352 A B u f s _36790 _36791)). Qed.
Lemma lem3491508 {A B : Type'} (_36791 : A) (_36790 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term343 A B u f _36791 s _36790.
Proof. exact (EQ_MP (@lem3491507 A B u f _36791 s _36790) (@lem3491506 A B _36790 _36791 f s t u h1)). Qed.
Lemma lem3491509 {A B : Type'} (_36792 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term353 A t u _36792.
Proof. exact (@lem3491324 A B f s t u h1 _36792). Qed.
Lemma lem3491510 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_36792 : A) : (term353 A t u _36792) = (term160 A t u _36792).
Proof. exact (eq_refl (term353 A t u _36792)). Qed.
Lemma lem3491512 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term350 A B x f s t _36793.
Proof. exact (@lem3491343 A B s x' x f t x'' h1 _36793). Qed.
Lemma lem3491513 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term350 A B x f s t _36793) = (term171 A B x f s t _36793).
Proof. exact (eq_refl (term350 A B x f s t _36793)). Qed.
Lemma lem3491515 {A B : Type'} (_36794 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term351 A B u f t _36794.
Proof. exact (@lem3491438 A B f t s u h1 _36794). Qed.
Lemma lem3491516 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) (_36794 : A) : (term351 A B u f t _36794) = (term346 A B u f t _36794).
Proof. exact (eq_refl (term351 A B u f t _36794)). Qed.
Lemma lem3491517 {A B : Type'} (_36794 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term346 A B u f t _36794.
Proof. exact (EQ_MP (@lem3491516 A B u f t _36794) (@lem3491515 A B _36794 f t s u h1)). Qed.
Lemma lem3491518 {A B : Type'} (_36794 : A) (_36795 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term352 A B u f t _36794 _36795.
Proof. exact (@lem3491517 A B _36794 f t s u h1 _36795). Qed.
Lemma lem3491519 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term352 A B u f t _36794 _36795) = (term343 A B u f _36795 t _36794).
Proof. exact (eq_refl (term352 A B u f t _36794 _36795)). Qed.
Lemma lem3491520 {A B : Type'} (_36795 : A) (_36794 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term343 A B u f _36795 t _36794.
Proof. exact (EQ_MP (@lem3491519 A B u f _36795 t _36794) (@lem3491518 A B _36794 _36795 f t s u h1)). Qed.
Lemma lem3491521 {A B : Type'} (_36796 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term353 A s u _36796.
Proof. exact (@lem3491451 A B f t s u h1 _36796). Qed.
Lemma lem3491522 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_36796 : A) : (term353 A s u _36796) = (term160 A s u _36796).
Proof. exact (eq_refl (term353 A s u _36796)). Qed.
Lemma lem3491525 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3490697 A B x' s x f t h1)). Qed.
Lemma lem3491535 {A B : Type'} (_36773 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term181 A B x f s _36773.
Proof. exact (EQ_MP (@lem3491453 A B x f s _36773) (@lem3491452 A B _36773 x f s h1)). Qed.
Lemma lem3491561 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3490697 A B x' s x f t h1)). Qed.
Lemma lem3491571 {A B : Type'} (_36777 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term188 A B x f s) : term181 A B x f s _36777.
Proof. exact (EQ_MP (@lem3491465 A B x f s _36777) (@lem3491464 A B _36777 x f s h1)). Qed.
Lemma lem3491597 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3490697 A B x' s x f t h1)). Qed.
Lemma lem3491607 {A B : Type'} (_36781 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term181 A B x f t _36781.
Proof. exact (EQ_MP (@lem3491477 A B x f t _36781) (@lem3491476 A B _36781 x f t h1)). Qed.
Lemma lem3491633 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3490697 A B x' s x f t h1)). Qed.
Lemma lem3491643 {A B : Type'} (_36785 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) : term181 A B x f t _36785.
Proof. exact (EQ_MP (@lem3491489 A B x f t _36785) (@lem3491488 A B _36785 x f t h1)). Qed.
Lemma lem3491677 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term171 A B x f s t _36789.
Proof. exact (EQ_MP (@lem3491501 A B x f s t _36789) (@lem3491500 A B _36789 s x' x f t x'' h1)). Qed.
Lemma lem3491679 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : x = (f x'').
Proof. exact (proj1 (@lem3490718 A B s x' x f t x'' h1)). Qed.
Lemma lem3491683 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3490719 A B s x' x f t x'' h1)). Qed.
Lemma lem3491689 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term343 A B u f _36791 s _36790) = (term354 A B u f _36791 s _36790).
Proof. exact (@lem3488504 (term317 A u _36790) (term140 A B _36790 f s _36791) (s _36790)). Qed.
Lemma lem3491696 {A B : Type'} (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term355 A B f _36791 s _36790) = (term356 A B f _36791 s _36790).
Proof. exact (@lem3488504 (term357 A B _36790 f _36791) (term317 A s _36791) (s _36790)). Qed.
Lemma lem3491697 {A : Type'} (u : A -> Prop) (_36790 : A) : (term150 A u _36790) = (term150 A u _36790).
Proof. exact (eq_refl (term150 A u _36790)). Qed.
Lemma lem3491700 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term354 A B u f _36791 s _36790) = (term358 A B u f _36791 s _36790).
Proof. exact (MK_COMB (@lem3491697 A u _36790) (@lem3491696 A B f _36791 s _36790)). Qed.
Lemma lem3491702 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term343 A B u f _36791 s _36790) = (term358 A B u f _36791 s _36790).
Proof. exact (TRANS (@lem3491689 A B u f _36791 s _36790) (@lem3491700 A B u f _36791 s _36790)). Qed.
Lemma lem3491719 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term171 A B x f s t _36793.
Proof. exact (EQ_MP (@lem3491513 A B x f s t _36793) (@lem3491512 A B _36793 s x' x f t x'' h1)). Qed.
Lemma lem3491721 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : x = (f x'').
Proof. exact (proj1 (@lem3490718 A B s x' x f t x'' h1)). Qed.
Lemma lem3491725 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3490719 A B s x' x f t x'' h1)). Qed.
Lemma lem3491731 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term343 A B u f _36795 t _36794) = (term354 A B u f _36795 t _36794).
Proof. exact (@lem3488504 (term317 A u _36794) (term140 A B _36794 f t _36795) (t _36794)). Qed.
Lemma lem3491738 {A B : Type'} (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term355 A B f _36795 t _36794) = (term356 A B f _36795 t _36794).
Proof. exact (@lem3488504 (term357 A B _36794 f _36795) (term317 A t _36795) (t _36794)). Qed.
Lemma lem3491739 {A : Type'} (u : A -> Prop) (_36794 : A) : (term150 A u _36794) = (term150 A u _36794).
Proof. exact (eq_refl (term150 A u _36794)). Qed.
Lemma lem3491742 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term354 A B u f _36795 t _36794) = (term358 A B u f _36795 t _36794).
Proof. exact (MK_COMB (@lem3491739 A u _36794) (@lem3491738 A B f _36795 t _36794)). Qed.
Lemma lem3491744 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term343 A B u f _36795 t _36794) = (term358 A B u f _36795 t _36794).
Proof. exact (TRANS (@lem3491731 A B u f _36795 t _36794) (@lem3491742 A B u f _36795 t _36794)). Qed.
Lemma lem3491794 {A B : Type'} (f : A -> B) (s : A -> Prop) (_36773 : A) : (term359 A B f s _36773) = (term359 A B f s _36773).
Proof. exact (eq_refl (term359 A B f s _36773)). Qed.
Lemma lem3491795 {A B : Type'} (_36773 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term360 A B f s _36773 x) = (term361 A B s _36773 f x').
Proof. exact (MK_COMB (@lem3491794 A B f s _36773) (@lem3491525 A B x' s x f t h1)). Qed.
Lemma lem3491796 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term361 A B s _36773 f x') = (term140 A B x' f s _36773).
Proof. exact (eq_refl (term361 A B s _36773 f x')). Qed.
Lemma lem3491797 {A B : Type'} (f : A -> B) (s : A -> Prop) (_36773 : A) (x : B) : (term362 A B f s _36773 x) = (term362 A B f s _36773 x).
Proof. exact (eq_refl (term362 A B f s _36773 x)). Qed.
Lemma lem3491798 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : ((term360 A B f s _36773 x) = (term361 A B s _36773 f x')) = ((term360 A B f s _36773 x) = (term140 A B x' f s _36773)).
Proof. exact (MK_COMB (@lem3491797 A B f s _36773 x) (@lem3491796 A B x' f s _36773)). Qed.
Lemma lem3491799 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term360 A B f s _36773 x) = (term181 A B x f s _36773).
Proof. exact (eq_refl (term360 A B f s _36773 x)). Qed.
Lemma lem3491800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491801 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term362 A B f s _36773 x) = (term363 A B x f s _36773).
Proof. exact (MK_COMB (@lem3491800) (@lem3491799 A B x f s _36773)). Qed.
Lemma lem3491802 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term140 A B x' f s _36773) = (term140 A B x' f s _36773).
Proof. exact (eq_refl (term140 A B x' f s _36773)). Qed.
Lemma lem3491803 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : ((term360 A B f s _36773 x) = (term140 A B x' f s _36773)) = ((term181 A B x f s _36773) = (term140 A B x' f s _36773)).
Proof. exact (MK_COMB (@lem3491801 A B x f s _36773) (@lem3491802 A B x' f s _36773)). Qed.
Lemma lem3491804 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : ((term360 A B f s _36773 x) = (term361 A B s _36773 f x')) = ((term181 A B x f s _36773) = (term140 A B x' f s _36773)).
Proof. exact (TRANS (@lem3491798 A B x x' f s _36773) (@lem3491803 A B x x' f s _36773)). Qed.
Lemma lem3491805 {A B : Type'} (_36773 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term181 A B x f s _36773) = (term140 A B x' f s _36773).
Proof. exact (EQ_MP (@lem3491804 A B x x' f s _36773) (@lem3491795 A B _36773 x' s x f t h1)). Qed.
Lemma lem3491806 {A B : Type'} (_36773 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term140 A B x' f s _36773.
Proof. exact (EQ_MP (@lem3491805 A B _36773 x' s x f t h2) (@lem3491535 A B _36773 x f s h1)). Qed.
Lemma lem3491877 {A B : Type'} (f : A -> B) (s : A -> Prop) (_36777 : A) : (term359 A B f s _36777) = (term359 A B f s _36777).
Proof. exact (eq_refl (term359 A B f s _36777)). Qed.
Lemma lem3491878 {A B : Type'} (_36777 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term360 A B f s _36777 x) = (term361 A B s _36777 f x').
Proof. exact (MK_COMB (@lem3491877 A B f s _36777) (@lem3491561 A B x' s x f t h1)). Qed.
Lemma lem3491879 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term361 A B s _36777 f x') = (term140 A B x' f s _36777).
Proof. exact (eq_refl (term361 A B s _36777 f x')). Qed.
Lemma lem3491880 {A B : Type'} (f : A -> B) (s : A -> Prop) (_36777 : A) (x : B) : (term362 A B f s _36777 x) = (term362 A B f s _36777 x).
Proof. exact (eq_refl (term362 A B f s _36777 x)). Qed.
Lemma lem3491881 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : ((term360 A B f s _36777 x) = (term361 A B s _36777 f x')) = ((term360 A B f s _36777 x) = (term140 A B x' f s _36777)).
Proof. exact (MK_COMB (@lem3491880 A B f s _36777 x) (@lem3491879 A B x' f s _36777)). Qed.
Lemma lem3491882 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term360 A B f s _36777 x) = (term181 A B x f s _36777).
Proof. exact (eq_refl (term360 A B f s _36777 x)). Qed.
Lemma lem3491883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491884 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term362 A B f s _36777 x) = (term363 A B x f s _36777).
Proof. exact (MK_COMB (@lem3491883) (@lem3491882 A B x f s _36777)). Qed.
Lemma lem3491885 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term140 A B x' f s _36777) = (term140 A B x' f s _36777).
Proof. exact (eq_refl (term140 A B x' f s _36777)). Qed.
Lemma lem3491886 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : ((term360 A B f s _36777 x) = (term140 A B x' f s _36777)) = ((term181 A B x f s _36777) = (term140 A B x' f s _36777)).
Proof. exact (MK_COMB (@lem3491884 A B x f s _36777) (@lem3491885 A B x' f s _36777)). Qed.
Lemma lem3491887 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : ((term360 A B f s _36777 x) = (term361 A B s _36777 f x')) = ((term181 A B x f s _36777) = (term140 A B x' f s _36777)).
Proof. exact (TRANS (@lem3491881 A B x x' f s _36777) (@lem3491886 A B x x' f s _36777)). Qed.
Lemma lem3491888 {A B : Type'} (_36777 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term181 A B x f s _36777) = (term140 A B x' f s _36777).
Proof. exact (EQ_MP (@lem3491887 A B x x' f s _36777) (@lem3491878 A B _36777 x' s x f t h1)). Qed.
Lemma lem3491889 {A B : Type'} (_36777 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term140 A B x' f s _36777.
Proof. exact (EQ_MP (@lem3491888 A B _36777 x' s x f t h2) (@lem3491571 A B _36777 x f s h1)). Qed.
Lemma lem3491960 {A B : Type'} (f : A -> B) (t : A -> Prop) (_36781 : A) : (term359 A B f t _36781) = (term359 A B f t _36781).
Proof. exact (eq_refl (term359 A B f t _36781)). Qed.
Lemma lem3491961 {A B : Type'} (_36781 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term360 A B f t _36781 x) = (term361 A B t _36781 f x').
Proof. exact (MK_COMB (@lem3491960 A B f t _36781) (@lem3491597 A B x' s x f t h1)). Qed.
Lemma lem3491962 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term361 A B t _36781 f x') = (term140 A B x' f t _36781).
Proof. exact (eq_refl (term361 A B t _36781 f x')). Qed.
Lemma lem3491963 {A B : Type'} (f : A -> B) (t : A -> Prop) (_36781 : A) (x : B) : (term362 A B f t _36781 x) = (term362 A B f t _36781 x).
Proof. exact (eq_refl (term362 A B f t _36781 x)). Qed.
Lemma lem3491964 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : ((term360 A B f t _36781 x) = (term361 A B t _36781 f x')) = ((term360 A B f t _36781 x) = (term140 A B x' f t _36781)).
Proof. exact (MK_COMB (@lem3491963 A B f t _36781 x) (@lem3491962 A B x' f t _36781)). Qed.
Lemma lem3491965 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term360 A B f t _36781 x) = (term181 A B x f t _36781).
Proof. exact (eq_refl (term360 A B f t _36781 x)). Qed.
Lemma lem3491966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3491967 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term362 A B f t _36781 x) = (term363 A B x f t _36781).
Proof. exact (MK_COMB (@lem3491966) (@lem3491965 A B x f t _36781)). Qed.
Lemma lem3491968 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term140 A B x' f t _36781) = (term140 A B x' f t _36781).
Proof. exact (eq_refl (term140 A B x' f t _36781)). Qed.
Lemma lem3491969 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : ((term360 A B f t _36781 x) = (term140 A B x' f t _36781)) = ((term181 A B x f t _36781) = (term140 A B x' f t _36781)).
Proof. exact (MK_COMB (@lem3491967 A B x f t _36781) (@lem3491968 A B x' f t _36781)). Qed.
Lemma lem3491970 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : ((term360 A B f t _36781 x) = (term361 A B t _36781 f x')) = ((term181 A B x f t _36781) = (term140 A B x' f t _36781)).
Proof. exact (TRANS (@lem3491964 A B x x' f t _36781) (@lem3491969 A B x x' f t _36781)). Qed.
Lemma lem3491971 {A B : Type'} (_36781 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term181 A B x f t _36781) = (term140 A B x' f t _36781).
Proof. exact (EQ_MP (@lem3491970 A B x x' f t _36781) (@lem3491961 A B _36781 x' s x f t h1)). Qed.
Lemma lem3491972 {A B : Type'} (_36781 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term140 A B x' f t _36781.
Proof. exact (EQ_MP (@lem3491971 A B _36781 x' s x f t h2) (@lem3491607 A B _36781 x f t h1)). Qed.
Lemma lem3492043 {A B : Type'} (f : A -> B) (t : A -> Prop) (_36785 : A) : (term359 A B f t _36785) = (term359 A B f t _36785).
Proof. exact (eq_refl (term359 A B f t _36785)). Qed.
Lemma lem3492044 {A B : Type'} (_36785 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term360 A B f t _36785 x) = (term361 A B t _36785 f x').
Proof. exact (MK_COMB (@lem3492043 A B f t _36785) (@lem3491633 A B x' s x f t h1)). Qed.
Lemma lem3492045 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term361 A B t _36785 f x') = (term140 A B x' f t _36785).
Proof. exact (eq_refl (term361 A B t _36785 f x')). Qed.
Lemma lem3492046 {A B : Type'} (f : A -> B) (t : A -> Prop) (_36785 : A) (x : B) : (term362 A B f t _36785 x) = (term362 A B f t _36785 x).
Proof. exact (eq_refl (term362 A B f t _36785 x)). Qed.
Lemma lem3492047 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : ((term360 A B f t _36785 x) = (term361 A B t _36785 f x')) = ((term360 A B f t _36785 x) = (term140 A B x' f t _36785)).
Proof. exact (MK_COMB (@lem3492046 A B f t _36785 x) (@lem3492045 A B x' f t _36785)). Qed.
Lemma lem3492048 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term360 A B f t _36785 x) = (term181 A B x f t _36785).
Proof. exact (eq_refl (term360 A B f t _36785 x)). Qed.
Lemma lem3492049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492050 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term362 A B f t _36785 x) = (term363 A B x f t _36785).
Proof. exact (MK_COMB (@lem3492049) (@lem3492048 A B x f t _36785)). Qed.
Lemma lem3492051 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term140 A B x' f t _36785) = (term140 A B x' f t _36785).
Proof. exact (eq_refl (term140 A B x' f t _36785)). Qed.
Lemma lem3492052 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : ((term360 A B f t _36785 x) = (term140 A B x' f t _36785)) = ((term181 A B x f t _36785) = (term140 A B x' f t _36785)).
Proof. exact (MK_COMB (@lem3492050 A B x f t _36785) (@lem3492051 A B x' f t _36785)). Qed.
Lemma lem3492053 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : ((term360 A B f t _36785 x) = (term361 A B t _36785 f x')) = ((term181 A B x f t _36785) = (term140 A B x' f t _36785)).
Proof. exact (TRANS (@lem3492047 A B x x' f t _36785) (@lem3492052 A B x x' f t _36785)). Qed.
Lemma lem3492054 {A B : Type'} (_36785 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : (term181 A B x f t _36785) = (term140 A B x' f t _36785).
Proof. exact (EQ_MP (@lem3492053 A B x x' f t _36785) (@lem3492044 A B _36785 x' s x f t h1)). Qed.
Lemma lem3492055 {A B : Type'} (_36785 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term140 A B x' f t _36785.
Proof. exact (EQ_MP (@lem3492054 A B _36785 x' s x f t h2) (@lem3491643 A B _36785 x f t h1)). Qed.
Lemma lem3492098 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term364 A B f s t _36789) = (term364 A B f s t _36789).
Proof. exact (eq_refl (term364 A B f s t _36789)). Qed.
Lemma lem3492099 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (term365 A B f s t _36789 x) = (term366 A B s t _36789 f x').
Proof. exact (MK_COMB (@lem3492098 A B f s t _36789) (@lem3491683 A B s x' x f t x'' h1)). Qed.
Lemma lem3492100 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term366 A B s t _36789 f x') = (term367 A B x' f s t _36789).
Proof. exact (eq_refl (term366 A B s t _36789 f x')). Qed.
Lemma lem3492101 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) (x : B) : (term368 A B f s t _36789 x) = (term368 A B f s t _36789 x).
Proof. exact (eq_refl (term368 A B f s t _36789 x)). Qed.
Lemma lem3492102 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : ((term365 A B f s t _36789 x) = (term366 A B s t _36789 f x')) = ((term365 A B f s t _36789 x) = (term367 A B x' f s t _36789)).
Proof. exact (MK_COMB (@lem3492101 A B f s t _36789 x) (@lem3492100 A B x' f s t _36789)). Qed.
Lemma lem3492103 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term365 A B f s t _36789 x) = (term171 A B x f s t _36789).
Proof. exact (eq_refl (term365 A B f s t _36789 x)). Qed.
Lemma lem3492104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492105 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term368 A B f s t _36789 x) = (term369 A B x f s t _36789).
Proof. exact (MK_COMB (@lem3492104) (@lem3492103 A B x f s t _36789)). Qed.
Lemma lem3492106 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term367 A B x' f s t _36789) = (term367 A B x' f s t _36789).
Proof. exact (eq_refl (term367 A B x' f s t _36789)). Qed.
Lemma lem3492107 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : ((term365 A B f s t _36789 x) = (term367 A B x' f s t _36789)) = ((term171 A B x f s t _36789) = (term367 A B x' f s t _36789)).
Proof. exact (MK_COMB (@lem3492105 A B x f s t _36789) (@lem3492106 A B x' f s t _36789)). Qed.
Lemma lem3492108 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : ((term365 A B f s t _36789 x) = (term366 A B s t _36789 f x')) = ((term171 A B x f s t _36789) = (term367 A B x' f s t _36789)).
Proof. exact (TRANS (@lem3492102 A B x x' f s t _36789) (@lem3492107 A B x x' f s t _36789)). Qed.
Lemma lem3492109 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (term171 A B x f s t _36789) = (term367 A B x' f s t _36789).
Proof. exact (EQ_MP (@lem3492108 A B x x' f s t _36789) (@lem3492099 A B _36789 s x' x f t x'' h1)). Qed.
Lemma lem3492110 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term367 A B x' f s t _36789.
Proof. exact (EQ_MP (@lem3492109 A B _36789 s x' x f t x'' h1) (@lem3491677 A B _36789 s x' x f t x'' h1)). Qed.
Lemma lem3492111 {A B : Type'} (f : A -> B) (x'' : A) : (term370 A B f x'') = (term370 A B f x'').
Proof. exact (eq_refl (term370 A B f x'')). Qed.
Lemma lem3492112 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (term371 A B f x'' x) = (term372 A B x'' f x').
Proof. exact (MK_COMB (@lem3492111 A B f x'') (@lem3491683 A B s x' x f t x'' h1)). Qed.
Lemma lem3492113 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term372 A B x'' f x') = ((f x') = (f x'')).
Proof. exact (eq_refl (term372 A B x'' f x')). Qed.
Lemma lem3492114 {A B : Type'} (f : A -> B) (x'' : A) (x : B) : (term373 A B f x'' x) = (term373 A B f x'' x).
Proof. exact (eq_refl (term373 A B f x'' x)). Qed.
Lemma lem3492115 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term371 A B f x'' x) = (term372 A B x'' f x')) = ((term371 A B f x'' x) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3492114 A B f x'' x) (@lem3492113 A B x' f x'')). Qed.
Lemma lem3492116 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term371 A B f x'' x) = (x = (f x'')).
Proof. exact (eq_refl (term371 A B f x'' x)). Qed.
Lemma lem3492117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492118 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term373 A B f x'' x) = (term374 A B x f x'').
Proof. exact (MK_COMB (@lem3492117) (@lem3492116 A B x f x'')). Qed.
Lemma lem3492119 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : ((f x') = (f x'')) = ((f x') = (f x'')).
Proof. exact (eq_refl ((f x') = (f x''))). Qed.
Lemma lem3492120 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term371 A B f x'' x) = ((f x') = (f x''))) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3492118 A B x f x'') (@lem3492119 A B x' f x'')). Qed.
Lemma lem3492121 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term371 A B f x'' x) = (term372 A B x'' f x')) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (TRANS (@lem3492115 A B x x' f x'') (@lem3492120 A B x x' f x'')). Qed.
Lemma lem3492122 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (x = (f x'')) = ((f x') = (f x'')).
Proof. exact (EQ_MP (@lem3492121 A B x x' f x'') (@lem3492112 A B s x' x f t x'' h1)). Qed.
Lemma lem3492165 {A B : Type'} (_36791 : A) (_36790 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term358 A B u f _36791 s _36790.
Proof. exact (EQ_MP (@lem3491702 A B u f _36791 s _36790) (@lem3491508 A B _36791 _36790 f s t u h1)). Qed.
Lemma lem3492179 {A B : Type'} (_36792 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term160 A t u _36792.
Proof. exact (EQ_MP (@lem3491510 A t u _36792) (@lem3491509 A B _36792 f s t u h1)). Qed.
Lemma lem3492194 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term364 A B f s t _36793) = (term364 A B f s t _36793).
Proof. exact (eq_refl (term364 A B f s t _36793)). Qed.
Lemma lem3492195 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (term365 A B f s t _36793 x) = (term366 A B s t _36793 f x').
Proof. exact (MK_COMB (@lem3492194 A B f s t _36793) (@lem3491725 A B s x' x f t x'' h1)). Qed.
Lemma lem3492196 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term366 A B s t _36793 f x') = (term367 A B x' f s t _36793).
Proof. exact (eq_refl (term366 A B s t _36793 f x')). Qed.
Lemma lem3492197 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) (x : B) : (term368 A B f s t _36793 x) = (term368 A B f s t _36793 x).
Proof. exact (eq_refl (term368 A B f s t _36793 x)). Qed.
Lemma lem3492198 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : ((term365 A B f s t _36793 x) = (term366 A B s t _36793 f x')) = ((term365 A B f s t _36793 x) = (term367 A B x' f s t _36793)).
Proof. exact (MK_COMB (@lem3492197 A B f s t _36793 x) (@lem3492196 A B x' f s t _36793)). Qed.
Lemma lem3492199 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term365 A B f s t _36793 x) = (term171 A B x f s t _36793).
Proof. exact (eq_refl (term365 A B f s t _36793 x)). Qed.
Lemma lem3492200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492201 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term368 A B f s t _36793 x) = (term369 A B x f s t _36793).
Proof. exact (MK_COMB (@lem3492200) (@lem3492199 A B x f s t _36793)). Qed.
Lemma lem3492202 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term367 A B x' f s t _36793) = (term367 A B x' f s t _36793).
Proof. exact (eq_refl (term367 A B x' f s t _36793)). Qed.
Lemma lem3492203 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : ((term365 A B f s t _36793 x) = (term367 A B x' f s t _36793)) = ((term171 A B x f s t _36793) = (term367 A B x' f s t _36793)).
Proof. exact (MK_COMB (@lem3492201 A B x f s t _36793) (@lem3492202 A B x' f s t _36793)). Qed.
Lemma lem3492204 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : ((term365 A B f s t _36793 x) = (term366 A B s t _36793 f x')) = ((term171 A B x f s t _36793) = (term367 A B x' f s t _36793)).
Proof. exact (TRANS (@lem3492198 A B x x' f s t _36793) (@lem3492203 A B x x' f s t _36793)). Qed.
Lemma lem3492205 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (term171 A B x f s t _36793) = (term367 A B x' f s t _36793).
Proof. exact (EQ_MP (@lem3492204 A B x x' f s t _36793) (@lem3492195 A B _36793 s x' x f t x'' h1)). Qed.
Lemma lem3492206 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term367 A B x' f s t _36793.
Proof. exact (EQ_MP (@lem3492205 A B _36793 s x' x f t x'' h1) (@lem3491719 A B _36793 s x' x f t x'' h1)). Qed.
Lemma lem3492207 {A B : Type'} (f : A -> B) (x'' : A) : (term370 A B f x'') = (term370 A B f x'').
Proof. exact (eq_refl (term370 A B f x'')). Qed.
Lemma lem3492208 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (term371 A B f x'' x) = (term372 A B x'' f x').
Proof. exact (MK_COMB (@lem3492207 A B f x'') (@lem3491725 A B s x' x f t x'' h1)). Qed.
Lemma lem3492209 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term372 A B x'' f x') = ((f x') = (f x'')).
Proof. exact (eq_refl (term372 A B x'' f x')). Qed.
Lemma lem3492210 {A B : Type'} (f : A -> B) (x'' : A) (x : B) : (term373 A B f x'' x) = (term373 A B f x'' x).
Proof. exact (eq_refl (term373 A B f x'' x)). Qed.
Lemma lem3492211 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term371 A B f x'' x) = (term372 A B x'' f x')) = ((term371 A B f x'' x) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3492210 A B f x'' x) (@lem3492209 A B x' f x'')). Qed.
Lemma lem3492212 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term371 A B f x'' x) = (x = (f x'')).
Proof. exact (eq_refl (term371 A B f x'' x)). Qed.
Lemma lem3492213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492214 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term373 A B f x'' x) = (term374 A B x f x'').
Proof. exact (MK_COMB (@lem3492213) (@lem3492212 A B x f x'')). Qed.
Lemma lem3492215 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : ((f x') = (f x'')) = ((f x') = (f x'')).
Proof. exact (eq_refl ((f x') = (f x''))). Qed.
Lemma lem3492216 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term371 A B f x'' x) = ((f x') = (f x''))) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3492214 A B x f x'') (@lem3492215 A B x' f x'')). Qed.
Lemma lem3492217 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term371 A B f x'' x) = (term372 A B x'' f x')) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (TRANS (@lem3492211 A B x x' f x'') (@lem3492216 A B x x' f x'')). Qed.
Lemma lem3492218 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (x = (f x'')) = ((f x') = (f x'')).
Proof. exact (EQ_MP (@lem3492217 A B x x' f x'') (@lem3492208 A B s x' x f t x'' h1)). Qed.
Lemma lem3492261 {A B : Type'} (_36795 : A) (_36794 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term358 A B u f _36795 t _36794.
Proof. exact (EQ_MP (@lem3491744 A B u f _36795 t _36794) (@lem3491520 A B _36795 _36794 f t s u h1)). Qed.
Lemma lem3492275 {A B : Type'} (_36796 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term160 A s u _36796.
Proof. exact (EQ_MP (@lem3491522 A s u _36796) (@lem3491521 A B _36796 f t s u h1)). Qed.
Lemma lem3492325 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3492326 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3492325 B x). Qed.
Lemma lem3492327 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3492326 B (f x')). Qed.
Lemma lem3492328 {A B : Type'} (f : A -> B) (x' : A) : term375 A B f x'.
Proof. exact (fun h0 : term376 A B f x' => @lem3492327 A B f x'). Qed.
Lemma lem3492330 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492331 {A B : Type'} (f : A -> B) (x' : A) : (term375 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3492330 ((f x') = (f x'))). Qed.
Lemma lem3492332 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3492331 A B f x') (@lem3492328 A B f x')). Qed.
Lemma lem3492334 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : s x'.
Proof. exact (proj1 (@lem3490698 A B x' s x f t h1)). Qed.
Lemma lem3492335 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term378 A s x'.
Proof. exact (fun h0 : term317 A s x' => @lem3492334 A B x' s x f t h1). Qed.
Lemma lem3492337 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492338 {A : Type'} (s : A -> Prop) (x' : A) : (term378 A s x') = (s x').
Proof. exact (@lem3492337 (s x')). Qed.
Lemma lem3492339 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : s x'.
Proof. exact (EQ_MP (@lem3492338 A s x') (@lem3492335 A B x' s x f t h1)). Qed.
Lemma lem3492341 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3492342 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term140 A B x' f s _36773) = (term139 A B x' f s _36773).
Proof. exact (@lem3492341 ((f x') = (f _36773)) (s _36773)). Qed.
Lemma lem3492344 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3492345 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term139 A B x' f s _36773) = (term381 A B x' f s _36773).
Proof. exact (@lem3492344 (term70 A B x' f s _36773)). Qed.
Lemma lem3492346 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36773 : A) : (term140 A B x' f s _36773) = (term381 A B x' f s _36773).
Proof. exact (TRANS (@lem3492342 A B x' f s _36773) (@lem3492345 A B x' f s _36773)). Qed.
Lemma lem3492348 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term382 A B f s x'.
Proof. exact (conj (@lem3492332 A B f x') (@lem3492339 A B x' s x f t h1)). Qed.
Lemma lem3492350 {A B : Type'} (_36773 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term381 A B x' f s _36773.
Proof. exact (EQ_MP (@lem3492346 A B x' f s _36773) (@lem3491806 A B _36773 x' s x f t h1 h2)). Qed.
Lemma lem3492351 {A B : Type'} (_36773 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term381 A B x' f s _36773.
Proof. exact (@lem3492350 A B _36773 x' s x f t h1 h2). Qed.
Lemma lem3492352 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term383 A B f s x'.
Proof. exact (@lem3492351 A B x' x' s x f t h1 h2). Qed.
Lemma lem3492355 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : False.
Proof. exact (@lem3492352 A B x' s x f t h1 h2 (@lem3492348 A B x' s x f t h2)). Qed.
Lemma lem3492356 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term384.
Proof. exact (fun h0 : ~ False => @lem3492355 A B x' s x f t h1 h2). Qed.
Lemma lem3492358 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492359 : term384 = False.
Proof. exact (@lem3492358 False). Qed.
Lemma lem3492410 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3492411 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3492410 B x). Qed.
Lemma lem3492412 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3492411 B (f x')). Qed.
Lemma lem3492413 {A B : Type'} (f : A -> B) (x' : A) : term375 A B f x'.
Proof. exact (fun h0 : term376 A B f x' => @lem3492412 A B f x'). Qed.
Lemma lem3492415 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492416 {A B : Type'} (f : A -> B) (x' : A) : (term375 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3492415 ((f x') = (f x'))). Qed.
Lemma lem3492417 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3492416 A B f x') (@lem3492413 A B f x')). Qed.
Lemma lem3492419 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : s x'.
Proof. exact (proj1 (@lem3490698 A B x' s x f t h1)). Qed.
Lemma lem3492420 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term378 A s x'.
Proof. exact (fun h0 : term317 A s x' => @lem3492419 A B x' s x f t h1). Qed.
Lemma lem3492422 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492423 {A : Type'} (s : A -> Prop) (x' : A) : (term378 A s x') = (s x').
Proof. exact (@lem3492422 (s x')). Qed.
Lemma lem3492424 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : s x'.
Proof. exact (EQ_MP (@lem3492423 A s x') (@lem3492420 A B x' s x f t h1)). Qed.
Lemma lem3492426 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3492427 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term140 A B x' f s _36777) = (term139 A B x' f s _36777).
Proof. exact (@lem3492426 ((f x') = (f _36777)) (s _36777)). Qed.
Lemma lem3492429 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3492430 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term139 A B x' f s _36777) = (term381 A B x' f s _36777).
Proof. exact (@lem3492429 (term70 A B x' f s _36777)). Qed.
Lemma lem3492431 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_36777 : A) : (term140 A B x' f s _36777) = (term381 A B x' f s _36777).
Proof. exact (TRANS (@lem3492427 A B x' f s _36777) (@lem3492430 A B x' f s _36777)). Qed.
Lemma lem3492433 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term382 A B f s x'.
Proof. exact (conj (@lem3492417 A B f x') (@lem3492424 A B x' s x f t h1)). Qed.
Lemma lem3492435 {A B : Type'} (_36777 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term381 A B x' f s _36777.
Proof. exact (EQ_MP (@lem3492431 A B x' f s _36777) (@lem3491889 A B _36777 x' s x f t h1 h2)). Qed.
Lemma lem3492436 {A B : Type'} (_36777 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term381 A B x' f s _36777.
Proof. exact (@lem3492435 A B _36777 x' s x f t h1 h2). Qed.
Lemma lem3492437 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term383 A B f s x'.
Proof. exact (@lem3492436 A B x' x' s x f t h1 h2). Qed.
Lemma lem3492440 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : False.
Proof. exact (@lem3492437 A B x' s x f t h1 h2 (@lem3492433 A B x' s x f t h2)). Qed.
Lemma lem3492441 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : term384.
Proof. exact (fun h0 : ~ False => @lem3492440 A B x' s x f t h1 h2). Qed.
Lemma lem3492443 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492444 : term384 = False.
Proof. exact (@lem3492443 False). Qed.
Lemma lem3492495 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3492496 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3492495 B x). Qed.
Lemma lem3492497 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3492496 B (f x')). Qed.
Lemma lem3492498 {A B : Type'} (f : A -> B) (x' : A) : term375 A B f x'.
Proof. exact (fun h0 : term376 A B f x' => @lem3492497 A B f x'). Qed.
Lemma lem3492500 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492501 {A B : Type'} (f : A -> B) (x' : A) : (term375 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3492500 ((f x') = (f x'))). Qed.
Lemma lem3492502 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3492501 A B f x') (@lem3492498 A B f x')). Qed.
Lemma lem3492504 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : t x'.
Proof. exact (proj2 (@lem3490698 A B x' s x f t h1)). Qed.
Lemma lem3492505 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term378 A t x'.
Proof. exact (fun h0 : term317 A t x' => @lem3492504 A B x' s x f t h1). Qed.
Lemma lem3492507 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492508 {A : Type'} (t : A -> Prop) (x' : A) : (term378 A t x') = (t x').
Proof. exact (@lem3492507 (t x')). Qed.
Lemma lem3492509 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : t x'.
Proof. exact (EQ_MP (@lem3492508 A t x') (@lem3492505 A B x' s x f t h1)). Qed.
Lemma lem3492511 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3492512 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term140 A B x' f t _36781) = (term139 A B x' f t _36781).
Proof. exact (@lem3492511 ((f x') = (f _36781)) (t _36781)). Qed.
Lemma lem3492514 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3492515 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term139 A B x' f t _36781) = (term381 A B x' f t _36781).
Proof. exact (@lem3492514 (term70 A B x' f t _36781)). Qed.
Lemma lem3492516 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36781 : A) : (term140 A B x' f t _36781) = (term381 A B x' f t _36781).
Proof. exact (TRANS (@lem3492512 A B x' f t _36781) (@lem3492515 A B x' f t _36781)). Qed.
Lemma lem3492518 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term382 A B f t x'.
Proof. exact (conj (@lem3492502 A B f x') (@lem3492509 A B x' s x f t h1)). Qed.
Lemma lem3492520 {A B : Type'} (_36781 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term381 A B x' f t _36781.
Proof. exact (EQ_MP (@lem3492516 A B x' f t _36781) (@lem3491972 A B _36781 x' s x f t h1 h2)). Qed.
Lemma lem3492521 {A B : Type'} (_36781 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term381 A B x' f t _36781.
Proof. exact (@lem3492520 A B _36781 x' s x f t h1 h2). Qed.
Lemma lem3492522 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term383 A B f t x'.
Proof. exact (@lem3492521 A B x' x' s x f t h1 h2). Qed.
Lemma lem3492525 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : False.
Proof. exact (@lem3492522 A B x' s x f t h1 h2 (@lem3492518 A B x' s x f t h2)). Qed.
Lemma lem3492526 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term384.
Proof. exact (fun h0 : ~ False => @lem3492525 A B x' s x f t h1 h2). Qed.
Lemma lem3492528 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492529 : term384 = False.
Proof. exact (@lem3492528 False). Qed.
Lemma lem3492580 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3492581 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3492580 B x). Qed.
Lemma lem3492582 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3492581 B (f x')). Qed.
Lemma lem3492583 {A B : Type'} (f : A -> B) (x' : A) : term375 A B f x'.
Proof. exact (fun h0 : term376 A B f x' => @lem3492582 A B f x'). Qed.
Lemma lem3492585 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492586 {A B : Type'} (f : A -> B) (x' : A) : (term375 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3492585 ((f x') = (f x'))). Qed.
Lemma lem3492587 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3492586 A B f x') (@lem3492583 A B f x')). Qed.
Lemma lem3492589 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : t x'.
Proof. exact (proj2 (@lem3490698 A B x' s x f t h1)). Qed.
Lemma lem3492590 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term378 A t x'.
Proof. exact (fun h0 : term317 A t x' => @lem3492589 A B x' s x f t h1). Qed.
Lemma lem3492592 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492593 {A : Type'} (t : A -> Prop) (x' : A) : (term378 A t x') = (t x').
Proof. exact (@lem3492592 (t x')). Qed.
Lemma lem3492594 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : t x'.
Proof. exact (EQ_MP (@lem3492593 A t x') (@lem3492590 A B x' s x f t h1)). Qed.
Lemma lem3492596 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3492597 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term140 A B x' f t _36785) = (term139 A B x' f t _36785).
Proof. exact (@lem3492596 ((f x') = (f _36785)) (t _36785)). Qed.
Lemma lem3492599 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3492600 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term139 A B x' f t _36785) = (term381 A B x' f t _36785).
Proof. exact (@lem3492599 (term70 A B x' f t _36785)). Qed.
Lemma lem3492601 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_36785 : A) : (term140 A B x' f t _36785) = (term381 A B x' f t _36785).
Proof. exact (TRANS (@lem3492597 A B x' f t _36785) (@lem3492600 A B x' f t _36785)). Qed.
Lemma lem3492603 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term217 A B x' s x f t) : term382 A B f t x'.
Proof. exact (conj (@lem3492587 A B f x') (@lem3492594 A B x' s x f t h1)). Qed.
Lemma lem3492605 {A B : Type'} (_36785 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term381 A B x' f t _36785.
Proof. exact (EQ_MP (@lem3492601 A B x' f t _36785) (@lem3492055 A B _36785 x' s x f t h1 h2)). Qed.
Lemma lem3492606 {A B : Type'} (_36785 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term381 A B x' f t _36785.
Proof. exact (@lem3492605 A B _36785 x' s x f t h1 h2). Qed.
Lemma lem3492607 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term383 A B f t x'.
Proof. exact (@lem3492606 A B x' x' s x f t h1 h2). Qed.
Lemma lem3492610 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : False.
Proof. exact (@lem3492607 A B x' s x f t h1 h2 (@lem3492603 A B x' s x f t h2)). Qed.
Lemma lem3492611 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : term384.
Proof. exact (fun h0 : ~ False => @lem3492610 A B x' s x f t h1 h2). Qed.
Lemma lem3492613 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492614 : term384 = False.
Proof. exact (@lem3492613 False). Qed.
Lemma lem3492661 {B : Type'} (x : B) (y : B) (z : B) : term385 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3492665 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3492122 A B s x' x f t x'' h1) (@lem3491679 A B s x' x f t x'' h1)). Qed.
Lemma lem3492666 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term386 A B x' f x''.
Proof. exact (fun h0 : term357 A B x' f x'' => @lem3492665 A B s x' x f t x'' h1). Qed.
Lemma lem3492668 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492669 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term386 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3492668 ((f x') = (f x''))). Qed.
Lemma lem3492670 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3492669 A B x' f x'') (@lem3492666 A B s x' x f t x'' h1)). Qed.
Lemma lem3492672 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : t x''.
Proof. exact (proj2 (@lem3490718 A B s x' x f t x'' h1)). Qed.
Lemma lem3492673 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term378 A t x''.
Proof. exact (fun h0 : term317 A t x'' => @lem3492672 A B s x' x f t x'' h1). Qed.
Lemma lem3492675 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492676 {A : Type'} (t : A -> Prop) (x'' : A) : (term378 A t x'') = (t x'').
Proof. exact (@lem3492675 (t x'')). Qed.
Lemma lem3492677 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3492676 A t x'') (@lem3492673 A B s x' x f t x'' h1)). Qed.
Lemma lem3492683 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3492684 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : (term160 A t u _36792) = (term387 A u t _36792).
Proof. exact (@lem3492683 (u _36792) (term317 A t _36792)). Qed.
Lemma lem3492690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492691 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : (term388 A t u _36792) = (term389 A u t _36792).
Proof. exact (MK_COMB (@lem3492690) (@lem3492684 A u t _36792)). Qed.
Lemma lem3492697 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : (term387 A u t _36792) = (term387 A u t _36792).
Proof. exact (eq_refl (term387 A u t _36792)). Qed.
Lemma lem3492698 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : ((term160 A t u _36792) = (term387 A u t _36792)) = ((term387 A u t _36792) = (term387 A u t _36792)).
Proof. exact (MK_COMB (@lem3492691 A u t _36792) (@lem3492697 A u t _36792)). Qed.
Lemma lem3492700 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3492701 (x : Prop) : (x = x) = True.
Proof. exact (@lem3492700 Prop x). Qed.
Lemma lem3492702 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : ((term387 A u t _36792) = (term387 A u t _36792)) = True.
Proof. exact (@lem3492701 (term387 A u t _36792)). Qed.
Lemma lem3492703 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : ((term160 A t u _36792) = (term387 A u t _36792)) = True.
Proof. exact (TRANS (@lem3492698 A u t _36792) (@lem3492702 A u t _36792)). Qed.
Lemma lem3492704 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : True = ((term160 A t u _36792) = (term387 A u t _36792)).
Proof. exact (SYM (@lem3492703 A u t _36792)). Qed.
Lemma lem3492705 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_36792 : A) : (term160 A t u _36792) = (term387 A u t _36792).
Proof. exact (EQ_MP (@lem3492704 A u t _36792) (@lem0)). Qed.
Lemma lem3492706 {A B : Type'} (_36792 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term387 A u t _36792.
Proof. exact (EQ_MP (@lem3492705 A u t _36792) (@lem3492179 A B _36792 f s t u h1)). Qed.
Lemma lem3492708 (b : Prop) (a : Prop) : (a \/ b) = (term390 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3492709 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_36792 : A) : (term387 A u t _36792) = (term391 A t u _36792).
Proof. exact (@lem3492708 (term317 A t _36792) (u _36792)). Qed.
Lemma lem3492711 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3492712 {A : Type'} (t : A -> Prop) (_36792 : A) : (term392 A t _36792) = (t _36792).
Proof. exact (@lem3492711 (t _36792)). Qed.
Lemma lem3492713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3492714 {A : Type'} (t : A -> Prop) (_36792 : A) : (term393 A t _36792) = (term84 A t _36792).
Proof. exact (MK_COMB (@lem3492713) (@lem3492712 A t _36792)). Qed.
Lemma lem3492715 {A : Type'} (u : A -> Prop) (_36792 : A) : (u _36792) = (u _36792).
Proof. exact (eq_refl (u _36792)). Qed.
Lemma lem3492716 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_36792 : A) : (term391 A t u _36792) = (term86 A t u _36792).
Proof. exact (MK_COMB (@lem3492714 A t _36792) (@lem3492715 A u _36792)). Qed.
Lemma lem3492717 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_36792 : A) : (term387 A u t _36792) = (term86 A t u _36792).
Proof. exact (TRANS (@lem3492709 A t u _36792) (@lem3492716 A t u _36792)). Qed.
Lemma lem3492720 {A B : Type'} (_36792 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term86 A t u _36792.
Proof. exact (EQ_MP (@lem3492717 A t u _36792) (@lem3492706 A B _36792 f s t u h1)). Qed.
Lemma lem3492721 {A B : Type'} (_36792 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term86 A t u _36792.
Proof. exact (@lem3492720 A B _36792 f s t u h1). Qed.
Lemma lem3492722 {A B : Type'} (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term86 A t u x''.
Proof. exact (@lem3492721 A B x'' f s t u h1). Qed.
Lemma lem3492725 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : u x''.
Proof. exact (@lem3492722 A B x'' f s t u h2 (@lem3492677 A B s x' x f t x'' h1)). Qed.
Lemma lem3492726 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : term378 A u x''.
Proof. exact (fun h0 : term317 A u x'' => @lem3492725 A B x' x x'' f s t u h1 h2). Qed.
Lemma lem3492728 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492729 {A : Type'} (u : A -> Prop) (x'' : A) : (term378 A u x'') = (u x'').
Proof. exact (@lem3492728 (u x'')). Qed.
Lemma lem3492730 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : u x''.
Proof. exact (EQ_MP (@lem3492729 A u x'') (@lem3492726 A B x' x x'' f s t u h1 h2)). Qed.
Lemma lem3492732 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3492122 A B s x' x f t x'' h1) (@lem3491679 A B s x' x f t x'' h1)). Qed.
Lemma lem3492733 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term386 A B x' f x''.
Proof. exact (fun h0 : term357 A B x' f x'' => @lem3492732 A B s x' x f t x'' h1). Qed.
Lemma lem3492735 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492736 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term386 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3492735 ((f x') = (f x''))). Qed.
Lemma lem3492737 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3492736 A B x' f x'') (@lem3492733 A B s x' x f t x'' h1)). Qed.
Lemma lem3492739 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3492740 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3492739 B x). Qed.
Lemma lem3492741 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3492740 B (f x')). Qed.
Lemma lem3492742 {A B : Type'} (f : A -> B) (x' : A) : term375 A B f x'.
Proof. exact (fun h0 : term376 A B f x' => @lem3492741 A B f x'). Qed.
Lemma lem3492744 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492745 {A B : Type'} (f : A -> B) (x' : A) : (term375 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3492744 ((f x') = (f x'))). Qed.
Lemma lem3492746 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3492745 A B f x') (@lem3492742 A B f x')). Qed.
Lemma lem3492764 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3492765 {B : Type'} (y : B) (x : B) (z : B) : (term394 B x y z) = (term395 B y x z).
Proof. exact (@lem3492764 (y = z) (term396 B x z)). Qed.
Lemma lem3492775 {B : Type'} (x : B) (y : B) : (term397 B x y) = (term397 B x y).
Proof. exact (eq_refl (term397 B x y)). Qed.
Lemma lem3492776 {B : Type'} (y : B) (x : B) (z : B) : (term385 B x y z) = (term398 B y x z).
Proof. exact (MK_COMB (@lem3492775 B x y) (@lem3492765 B y x z)). Qed.
Lemma lem3492780 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3492781 {B : Type'} (y : B) (x : B) (z : B) : (term398 B y x z) = (term399 B y x z).
Proof. exact (@lem3492780 (y = z) (term396 B x y) (term396 B x z)). Qed.
Lemma lem3492803 {B : Type'} (y : B) (x : B) (z : B) : (term385 B x y z) = (term399 B y x z).
Proof. exact (TRANS (@lem3492776 B y x z) (@lem3492781 B y x z)). Qed.
Lemma lem3492804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492805 {B : Type'} (y : B) (x : B) (z : B) : (term400 B x y z) = (term401 B y x z).
Proof. exact (MK_COMB (@lem3492804) (@lem3492803 B y x z)). Qed.
Lemma lem3492827 {B : Type'} (y : B) (x : B) (z : B) : (term399 B y x z) = (term399 B y x z).
Proof. exact (eq_refl (term399 B y x z)). Qed.
Lemma lem3492828 {B : Type'} (y : B) (x : B) (z : B) : ((term385 B x y z) = (term399 B y x z)) = ((term399 B y x z) = (term399 B y x z)).
Proof. exact (MK_COMB (@lem3492805 B y x z) (@lem3492827 B y x z)). Qed.
Lemma lem3492830 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3492831 (x : Prop) : (x = x) = True.
Proof. exact (@lem3492830 Prop x). Qed.
Lemma lem3492832 {B : Type'} (y : B) (x : B) (z : B) : ((term399 B y x z) = (term399 B y x z)) = True.
Proof. exact (@lem3492831 (term399 B y x z)). Qed.
Lemma lem3492833 {B : Type'} (y : B) (x : B) (z : B) : ((term385 B x y z) = (term399 B y x z)) = True.
Proof. exact (TRANS (@lem3492828 B y x z) (@lem3492832 B y x z)). Qed.
Lemma lem3492834 {B : Type'} (y : B) (x : B) (z : B) : True = ((term385 B x y z) = (term399 B y x z)).
Proof. exact (SYM (@lem3492833 B y x z)). Qed.
Lemma lem3492835 {B : Type'} (y : B) (x : B) (z : B) : (term385 B x y z) = (term399 B y x z).
Proof. exact (EQ_MP (@lem3492834 B y x z) (@lem0)). Qed.
Lemma lem3492836 {B : Type'} (y : B) (x : B) (z : B) : term399 B y x z.
Proof. exact (EQ_MP (@lem3492835 B y x z) (@lem3492661 B x y z)). Qed.
Lemma lem3492838 (b : Prop) (a : Prop) : (a \/ b) = (term390 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3492839 {B : Type'} (x : B) (y : B) (z : B) : (term399 B y x z) = (term402 B x y z).
Proof. exact (@lem3492838 (term403 B y x z) (y = z)). Qed.
Lemma lem3492841 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3492842 {B : Type'} (y : B) (x : B) (z : B) : (term406 B y x z) = (term407 B y x z).
Proof. exact (@lem3492841 (term396 B x y) (term396 B x z)). Qed.
Lemma lem3492844 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3492845 {B : Type'} (x : B) (y : B) : (term408 B x y) = (x = y).
Proof. exact (@lem3492844 (x = y)). Qed.
Lemma lem3492846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3492847 {B : Type'} (x : B) (y : B) : (term409 B x y) = (term410 B x y).
Proof. exact (MK_COMB (@lem3492846) (@lem3492845 B x y)). Qed.
Lemma lem3492849 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3492850 {B : Type'} (x : B) (z : B) : (term408 B x z) = (x = z).
Proof. exact (@lem3492849 (x = z)). Qed.
Lemma lem3492851 {B : Type'} (y : B) (x : B) (z : B) : (term407 B y x z) = (term411 B y x z).
Proof. exact (MK_COMB (@lem3492847 B x y) (@lem3492850 B x z)). Qed.
Lemma lem3492852 {B : Type'} (y : B) (x : B) (z : B) : (term406 B y x z) = (term411 B y x z).
Proof. exact (TRANS (@lem3492842 B y x z) (@lem3492851 B y x z)). Qed.
Lemma lem3492853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3492854 {B : Type'} (y : B) (x : B) (z : B) : (term412 B y x z) = (term413 B y x z).
Proof. exact (MK_COMB (@lem3492853) (@lem3492852 B y x z)). Qed.
Lemma lem3492855 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3492856 {B : Type'} (x : B) (y : B) (z : B) : (term402 B x y z) = (term414 B x y z).
Proof. exact (MK_COMB (@lem3492854 B y x z) (@lem3492855 B y z)). Qed.
Lemma lem3492857 {B : Type'} (x : B) (y : B) (z : B) : (term399 B y x z) = (term414 B x y z).
Proof. exact (TRANS (@lem3492839 B x y z) (@lem3492856 B x y z)). Qed.
Lemma lem3492859 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term415 A B x'' f x'.
Proof. exact (conj (@lem3492737 A B s x' x f t x'' h1) (@lem3492746 A B f x')). Qed.
Lemma lem3492861 {B : Type'} (x : B) (y : B) (z : B) : term414 B x y z.
Proof. exact (EQ_MP (@lem3492857 B x y z) (@lem3492836 B y x z)). Qed.
Lemma lem3492862 {B : Type'} (x : B) (y : B) (z : B) : term414 B x y z.
Proof. exact (@lem3492861 B x y z). Qed.
Lemma lem3492863 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : term416 A B x'' f x'.
Proof. exact (@lem3492862 B (f x') (f x'') (f x')). Qed.
Lemma lem3492866 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x'') = (f x').
Proof. exact (@lem3492863 A B x'' f x' (@lem3492859 A B s x' x f t x'' h1)). Qed.
Lemma lem3492867 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term386 A B x'' f x'.
Proof. exact (fun h0 : term357 A B x'' f x' => @lem3492866 A B s x' x f t x'' h1). Qed.
Lemma lem3492869 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492870 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : (term386 A B x'' f x') = ((f x'') = (f x')).
Proof. exact (@lem3492869 ((f x'') = (f x'))). Qed.
Lemma lem3492871 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x'') = (f x').
Proof. exact (EQ_MP (@lem3492870 A B x'' f x') (@lem3492867 A B s x' x f t x'' h1)). Qed.
Lemma lem3492873 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : s x'.
Proof. exact (proj2 (@lem3490719 A B s x' x f t x'' h1)). Qed.
Lemma lem3492874 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term378 A s x'.
Proof. exact (fun h0 : term317 A s x' => @lem3492873 A B s x' x f t x'' h1). Qed.
Lemma lem3492876 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3492877 {A : Type'} (s : A -> Prop) (x' : A) : (term378 A s x') = (s x').
Proof. exact (@lem3492876 (s x')). Qed.
Lemma lem3492878 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3492877 A s x') (@lem3492874 A B s x' x f t x'' h1)). Qed.
Lemma lem3492894 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3492895 {A B : Type'} (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term356 A B f _36791 s _36790) = (term417 A B f _36791 s _36790).
Proof. exact (@lem3492894 (term317 A s _36791) (term357 A B _36790 f _36791) (s _36790)). Qed.
Lemma lem3492909 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3492910 {A B : Type'} (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term418 A B f _36791 s _36790) = (term419 A B s _36790 f _36791).
Proof. exact (@lem3492909 (s _36790) (term357 A B _36790 f _36791)). Qed.
Lemma lem3492918 {A : Type'} (s : A -> Prop) (_36791 : A) : (term150 A s _36791) = (term150 A s _36791).
Proof. exact (eq_refl (term150 A s _36791)). Qed.
Lemma lem3492919 {A B : Type'} (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term417 A B f _36791 s _36790) = (term420 A B s _36790 f _36791).
Proof. exact (MK_COMB (@lem3492918 A s _36791) (@lem3492910 A B s _36790 f _36791)). Qed.
Lemma lem3492923 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3492924 {A B : Type'} (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term420 A B s _36790 f _36791) = (term421 A B s _36790 f _36791).
Proof. exact (@lem3492923 (s _36790) (term317 A s _36791) (term357 A B _36790 f _36791)). Qed.
Lemma lem3492942 {A B : Type'} (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term417 A B f _36791 s _36790) = (term421 A B s _36790 f _36791).
Proof. exact (TRANS (@lem3492919 A B s _36790 f _36791) (@lem3492924 A B s _36790 f _36791)). Qed.
Lemma lem3492943 {A B : Type'} (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term356 A B f _36791 s _36790) = (term421 A B s _36790 f _36791).
Proof. exact (TRANS (@lem3492895 A B f _36791 s _36790) (@lem3492942 A B s _36790 f _36791)). Qed.
Lemma lem3492944 {A : Type'} (u : A -> Prop) (_36790 : A) : (term150 A u _36790) = (term150 A u _36790).
Proof. exact (eq_refl (term150 A u _36790)). Qed.
Lemma lem3492945 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term358 A B u f _36791 s _36790) = (term422 A B u s _36790 f _36791).
Proof. exact (MK_COMB (@lem3492944 A u _36790) (@lem3492943 A B s _36790 f _36791)). Qed.
Lemma lem3492949 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3492950 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term422 A B u s _36790 f _36791) = (term423 A B u s _36790 f _36791).
Proof. exact (@lem3492949 (s _36790) (term317 A u _36790) (term424 A B s _36790 f _36791)). Qed.
Lemma lem3492964 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3492965 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term425 A B u s _36790 f _36791) = (term426 A B s u _36790 f _36791).
Proof. exact (@lem3492964 (term317 A s _36791) (term317 A u _36790) (term357 A B _36790 f _36791)). Qed.
Lemma lem3492983 {A : Type'} (s : A -> Prop) (_36790 : A) : (term427 A s _36790) = (term427 A s _36790).
Proof. exact (eq_refl (term427 A s _36790)). Qed.
Lemma lem3492984 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term423 A B u s _36790 f _36791) = (term428 A B s u _36790 f _36791).
Proof. exact (MK_COMB (@lem3492983 A s _36790) (@lem3492965 A B s u _36790 f _36791)). Qed.
Lemma lem3492995 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term422 A B u s _36790 f _36791) = (term428 A B s u _36790 f _36791).
Proof. exact (TRANS (@lem3492950 A B u s _36790 f _36791) (@lem3492984 A B s u _36790 f _36791)). Qed.
Lemma lem3492996 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term358 A B u f _36791 s _36790) = (term428 A B s u _36790 f _36791).
Proof. exact (TRANS (@lem3492945 A B u s _36790 f _36791) (@lem3492995 A B s u _36790 f _36791)). Qed.
Lemma lem3492997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3492998 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term429 A B u f _36791 s _36790) = (term430 A B s u _36790 f _36791).
Proof. exact (MK_COMB (@lem3492997) (@lem3492996 A B s u _36790 f _36791)). Qed.
Lemma lem3493022 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3493023 {A B : Type'} (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term140 A B _36790 f s _36791) = (term424 A B s _36790 f _36791).
Proof. exact (@lem3493022 (term317 A s _36791) (term357 A B _36790 f _36791)). Qed.
Lemma lem3493031 {A : Type'} (u : A -> Prop) (_36790 : A) : (term150 A u _36790) = (term150 A u _36790).
Proof. exact (eq_refl (term150 A u _36790)). Qed.
Lemma lem3493032 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term324 A B u _36790 f s _36791) = (term425 A B u s _36790 f _36791).
Proof. exact (MK_COMB (@lem3493031 A u _36790) (@lem3493023 A B s _36790 f _36791)). Qed.
Lemma lem3493036 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3493037 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term425 A B u s _36790 f _36791) = (term426 A B s u _36790 f _36791).
Proof. exact (@lem3493036 (term317 A s _36791) (term317 A u _36790) (term357 A B _36790 f _36791)). Qed.
Lemma lem3493055 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term324 A B u _36790 f s _36791) = (term426 A B s u _36790 f _36791).
Proof. exact (TRANS (@lem3493032 A B u s _36790 f _36791) (@lem3493037 A B s u _36790 f _36791)). Qed.
Lemma lem3493056 {A : Type'} (s : A -> Prop) (_36790 : A) : (term427 A s _36790) = (term427 A s _36790).
Proof. exact (eq_refl (term427 A s _36790)). Qed.
Lemma lem3493057 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : (term431 A B u _36790 f s _36791) = (term428 A B s u _36790 f _36791).
Proof. exact (MK_COMB (@lem3493056 A s _36790) (@lem3493055 A B s u _36790 f _36791)). Qed.
Lemma lem3493068 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : ((term358 A B u f _36791 s _36790) = (term431 A B u _36790 f s _36791)) = ((term428 A B s u _36790 f _36791) = (term428 A B s u _36790 f _36791)).
Proof. exact (MK_COMB (@lem3492998 A B s u _36790 f _36791) (@lem3493057 A B s u _36790 f _36791)). Qed.
Lemma lem3493070 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3493071 (x : Prop) : (x = x) = True.
Proof. exact (@lem3493070 Prop x). Qed.
Lemma lem3493072 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (_36790 : A) (f : A -> B) (_36791 : A) : ((term428 A B s u _36790 f _36791) = (term428 A B s u _36790 f _36791)) = True.
Proof. exact (@lem3493071 (term428 A B s u _36790 f _36791)). Qed.
Lemma lem3493073 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : ((term358 A B u f _36791 s _36790) = (term431 A B u _36790 f s _36791)) = True.
Proof. exact (TRANS (@lem3493068 A B s u _36790 f _36791) (@lem3493072 A B s u _36790 f _36791)). Qed.
Lemma lem3493074 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : True = ((term358 A B u f _36791 s _36790) = (term431 A B u _36790 f s _36791)).
Proof. exact (SYM (@lem3493073 A B u _36790 f s _36791)). Qed.
Lemma lem3493075 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term358 A B u f _36791 s _36790) = (term431 A B u _36790 f s _36791).
Proof. exact (EQ_MP (@lem3493074 A B u _36790 f s _36791) (@lem0)). Qed.
Lemma lem3493076 {A B : Type'} (_36790 : A) (_36791 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term431 A B u _36790 f s _36791.
Proof. exact (EQ_MP (@lem3493075 A B u _36790 f s _36791) (@lem3492165 A B _36791 _36790 f s t u h1)). Qed.
Lemma lem3493078 (b : Prop) (a : Prop) : (a \/ b) = (term390 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3493079 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term431 A B u _36790 f s _36791) = (term432 A B u f _36791 s _36790).
Proof. exact (@lem3493078 (term324 A B u _36790 f s _36791) (s _36790)). Qed.
Lemma lem3493081 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3493082 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term433 A B u _36790 f s _36791) = (term434 A B u _36790 f s _36791).
Proof. exact (@lem3493081 (term317 A u _36790) (term140 A B _36790 f s _36791)). Qed.
Lemma lem3493084 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493085 {A : Type'} (u : A -> Prop) (_36790 : A) : (term392 A u _36790) = (u _36790).
Proof. exact (@lem3493084 (u _36790)). Qed.
Lemma lem3493086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3493087 {A : Type'} (u : A -> Prop) (_36790 : A) : (term435 A u _36790) = (term63 A u _36790).
Proof. exact (MK_COMB (@lem3493086) (@lem3493085 A u _36790)). Qed.
Lemma lem3493089 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3493090 {A B : Type'} (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term436 A B _36790 f s _36791) = (term437 A B _36790 f s _36791).
Proof. exact (@lem3493089 (term357 A B _36790 f _36791) (term317 A s _36791)). Qed.
Lemma lem3493092 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493093 {A B : Type'} (_36790 : A) (f : A -> B) (_36791 : A) : (term438 A B _36790 f _36791) = ((f _36790) = (f _36791)).
Proof. exact (@lem3493092 ((f _36790) = (f _36791))). Qed.
Lemma lem3493094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3493095 {A B : Type'} (_36790 : A) (f : A -> B) (_36791 : A) : (term439 A B _36790 f _36791) = (term68 A B _36790 f _36791).
Proof. exact (MK_COMB (@lem3493094) (@lem3493093 A B _36790 f _36791)). Qed.
Lemma lem3493097 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493098 {A : Type'} (s : A -> Prop) (_36791 : A) : (term392 A s _36791) = (s _36791).
Proof. exact (@lem3493097 (s _36791)). Qed.
Lemma lem3493099 {A B : Type'} (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term437 A B _36790 f s _36791) = (term70 A B _36790 f s _36791).
Proof. exact (MK_COMB (@lem3493095 A B _36790 f _36791) (@lem3493098 A s _36791)). Qed.
Lemma lem3493100 {A B : Type'} (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term436 A B _36790 f s _36791) = (term70 A B _36790 f s _36791).
Proof. exact (TRANS (@lem3493090 A B _36790 f s _36791) (@lem3493099 A B _36790 f s _36791)). Qed.
Lemma lem3493101 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term434 A B u _36790 f s _36791) = (term440 A B u _36790 f s _36791).
Proof. exact (MK_COMB (@lem3493087 A u _36790) (@lem3493100 A B _36790 f s _36791)). Qed.
Lemma lem3493102 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term433 A B u _36790 f s _36791) = (term440 A B u _36790 f s _36791).
Proof. exact (TRANS (@lem3493082 A B u _36790 f s _36791) (@lem3493101 A B u _36790 f s _36791)). Qed.
Lemma lem3493103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3493104 {A B : Type'} (u : A -> Prop) (_36790 : A) (f : A -> B) (s : A -> Prop) (_36791 : A) : (term441 A B u _36790 f s _36791) = (term442 A B u _36790 f s _36791).
Proof. exact (MK_COMB (@lem3493103) (@lem3493102 A B u _36790 f s _36791)). Qed.
Lemma lem3493105 {A : Type'} (s : A -> Prop) (_36790 : A) : (s _36790) = (s _36790).
Proof. exact (eq_refl (s _36790)). Qed.
Lemma lem3493106 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term432 A B u f _36791 s _36790) = (term443 A B u f _36791 s _36790).
Proof. exact (MK_COMB (@lem3493104 A B u _36790 f s _36791) (@lem3493105 A s _36790)). Qed.
Lemma lem3493107 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36791 : A) (s : A -> Prop) (_36790 : A) : (term431 A B u _36790 f s _36791) = (term443 A B u f _36791 s _36790).
Proof. exact (TRANS (@lem3493079 A B u f _36791 s _36790) (@lem3493106 A B u f _36791 s _36790)). Qed.
Lemma lem3493109 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term70 A B x'' f s x'.
Proof. exact (conj (@lem3492871 A B s x' x f t x'' h1) (@lem3492878 A B s x' x f t x'' h1)). Qed.
Lemma lem3493110 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : term440 A B u x'' f s x'.
Proof. exact (conj (@lem3492730 A B x' x x'' f s t u h1 h2) (@lem3493109 A B s x' x f t x'' h1)). Qed.
Lemma lem3493112 {A B : Type'} (_36791 : A) (_36790 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term443 A B u f _36791 s _36790.
Proof. exact (EQ_MP (@lem3493107 A B u f _36791 s _36790) (@lem3493076 A B _36790 _36791 f s t u h1)). Qed.
Lemma lem3493113 {A B : Type'} (_36791 : A) (_36790 : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term443 A B u f _36791 s _36790.
Proof. exact (@lem3493112 A B _36791 _36790 f s t u h1). Qed.
Lemma lem3493114 {A B : Type'} (x' : A) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term164 A B f s t u) : term443 A B u f x' s x''.
Proof. exact (@lem3493113 A B x' x'' f s t u h1). Qed.
Lemma lem3493117 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : s x''.
Proof. exact (@lem3493114 A B x' x'' f s t u h2 (@lem3493110 A B x' x x'' f s t u h1 h2)). Qed.
Lemma lem3493118 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : term378 A s x''.
Proof. exact (fun h0 : term317 A s x'' => @lem3493117 A B x' x x'' f s t u h1 h2). Qed.
Lemma lem3493120 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493121 {A : Type'} (s : A -> Prop) (x'' : A) : (term378 A s x'') = (s x'').
Proof. exact (@lem3493120 (s x'')). Qed.
Lemma lem3493122 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : s x''.
Proof. exact (EQ_MP (@lem3493121 A s x'') (@lem3493118 A B x' x x'' f s t u h1 h2)). Qed.
Lemma lem3493124 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : t x''.
Proof. exact (proj2 (@lem3490718 A B s x' x f t x'' h1)). Qed.
Lemma lem3493125 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term378 A t x''.
Proof. exact (fun h0 : term317 A t x'' => @lem3493124 A B s x' x f t x'' h1). Qed.
Lemma lem3493127 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493128 {A : Type'} (t : A -> Prop) (x'' : A) : (term378 A t x'') = (t x'').
Proof. exact (@lem3493127 (t x'')). Qed.
Lemma lem3493129 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3493128 A t x'') (@lem3493125 A B s x' x f t x'' h1)). Qed.
Lemma lem3493131 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3493132 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term168 A s t _36789) = (term167 A s t _36789).
Proof. exact (@lem3493131 (s _36789) (t _36789)). Qed.
Lemma lem3493133 {A B : Type'} (x' : A) (f : A -> B) (_36789 : A) : (term444 A B x' f _36789) = (term444 A B x' f _36789).
Proof. exact (eq_refl (term444 A B x' f _36789)). Qed.
Lemma lem3493134 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term367 A B x' f s t _36789) = (term445 A B x' f s t _36789).
Proof. exact (MK_COMB (@lem3493133 A B x' f _36789) (@lem3493132 A s t _36789)). Qed.
Lemma lem3493136 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3493137 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term445 A B x' f s t _36789) = (term446 A B x' f s t _36789).
Proof. exact (@lem3493136 ((f x') = (f _36789)) (term98 A s t _36789)). Qed.
Lemma lem3493138 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term367 A B x' f s t _36789) = (term446 A B x' f s t _36789).
Proof. exact (TRANS (@lem3493134 A B x' f s t _36789) (@lem3493137 A B x' f s t _36789)). Qed.
Lemma lem3493140 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3493141 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term446 A B x' f s t _36789) = (term447 A B x' f s t _36789).
Proof. exact (@lem3493140 (term448 A B x' f s t _36789)). Qed.
Lemma lem3493142 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36789 : A) : (term367 A B x' f s t _36789) = (term447 A B x' f s t _36789).
Proof. exact (TRANS (@lem3493138 A B x' f s t _36789) (@lem3493141 A B x' f s t _36789)). Qed.
Lemma lem3493144 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : term98 A s t x''.
Proof. exact (conj (@lem3493122 A B x' x x'' f s t u h1 h2) (@lem3493129 A B s x' x f t x'' h1)). Qed.
Lemma lem3493145 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : term448 A B x' f s t x''.
Proof. exact (conj (@lem3492670 A B s x' x f t x'' h1) (@lem3493144 A B x' x x'' f s t u h1 h2)). Qed.
Lemma lem3493147 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term447 A B x' f s t _36789.
Proof. exact (EQ_MP (@lem3493142 A B x' f s t _36789) (@lem3492110 A B _36789 s x' x f t x'' h1)). Qed.
Lemma lem3493148 {A B : Type'} (_36789 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term447 A B x' f s t _36789.
Proof. exact (@lem3493147 A B _36789 s x' x f t x'' h1). Qed.
Lemma lem3493149 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term447 A B x' f s t x''.
Proof. exact (@lem3493148 A B x'' s x' x f t x'' h1). Qed.
Lemma lem3493152 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : False.
Proof. exact (@lem3493149 A B s x' x f t x'' h1 (@lem3493145 A B x' x x'' f s t u h1 h2)). Qed.
Lemma lem3493153 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : term384.
Proof. exact (fun h0 : ~ False => @lem3493152 A B x' x x'' f s t u h1 h2). Qed.
Lemma lem3493155 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493156 : term384 = False.
Proof. exact (@lem3493155 False). Qed.
Lemma lem3493207 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3493208 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3493207 B x). Qed.
Lemma lem3493209 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3493208 B (f x')). Qed.
Lemma lem3493210 {A B : Type'} (f : A -> B) (x' : A) : term375 A B f x'.
Proof. exact (fun h0 : term376 A B f x' => @lem3493209 A B f x'). Qed.
Lemma lem3493212 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493213 {A B : Type'} (f : A -> B) (x' : A) : (term375 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3493212 ((f x') = (f x'))). Qed.
Lemma lem3493214 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3493213 A B f x') (@lem3493210 A B f x')). Qed.
Lemma lem3493216 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : s x'.
Proof. exact (proj2 (@lem3490719 A B s x' x f t x'' h1)). Qed.
Lemma lem3493217 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term378 A s x'.
Proof. exact (fun h0 : term317 A s x' => @lem3493216 A B s x' x f t x'' h1). Qed.
Lemma lem3493219 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493220 {A : Type'} (s : A -> Prop) (x' : A) : (term378 A s x') = (s x').
Proof. exact (@lem3493219 (s x')). Qed.
Lemma lem3493221 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3493220 A s x') (@lem3493217 A B s x' x f t x'' h1)). Qed.
Lemma lem3493223 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : s x'.
Proof. exact (proj2 (@lem3490719 A B s x' x f t x'' h1)). Qed.
Lemma lem3493224 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term378 A s x'.
Proof. exact (fun h0 : term317 A s x' => @lem3493223 A B s x' x f t x'' h1). Qed.
Lemma lem3493226 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493227 {A : Type'} (s : A -> Prop) (x' : A) : (term378 A s x') = (s x').
Proof. exact (@lem3493226 (s x')). Qed.
Lemma lem3493228 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3493227 A s x') (@lem3493224 A B s x' x f t x'' h1)). Qed.
Lemma lem3493234 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3493235 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : (term160 A s u _36796) = (term387 A u s _36796).
Proof. exact (@lem3493234 (u _36796) (term317 A s _36796)). Qed.
Lemma lem3493241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3493242 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : (term388 A s u _36796) = (term389 A u s _36796).
Proof. exact (MK_COMB (@lem3493241) (@lem3493235 A u s _36796)). Qed.
Lemma lem3493248 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : (term387 A u s _36796) = (term387 A u s _36796).
Proof. exact (eq_refl (term387 A u s _36796)). Qed.
Lemma lem3493249 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : ((term160 A s u _36796) = (term387 A u s _36796)) = ((term387 A u s _36796) = (term387 A u s _36796)).
Proof. exact (MK_COMB (@lem3493242 A u s _36796) (@lem3493248 A u s _36796)). Qed.
Lemma lem3493251 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3493252 (x : Prop) : (x = x) = True.
Proof. exact (@lem3493251 Prop x). Qed.
Lemma lem3493253 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : ((term387 A u s _36796) = (term387 A u s _36796)) = True.
Proof. exact (@lem3493252 (term387 A u s _36796)). Qed.
Lemma lem3493254 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : ((term160 A s u _36796) = (term387 A u s _36796)) = True.
Proof. exact (TRANS (@lem3493249 A u s _36796) (@lem3493253 A u s _36796)). Qed.
Lemma lem3493255 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : True = ((term160 A s u _36796) = (term387 A u s _36796)).
Proof. exact (SYM (@lem3493254 A u s _36796)). Qed.
Lemma lem3493256 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_36796 : A) : (term160 A s u _36796) = (term387 A u s _36796).
Proof. exact (EQ_MP (@lem3493255 A u s _36796) (@lem0)). Qed.
Lemma lem3493257 {A B : Type'} (_36796 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term387 A u s _36796.
Proof. exact (EQ_MP (@lem3493256 A u s _36796) (@lem3492275 A B _36796 f t s u h1)). Qed.
Lemma lem3493259 (b : Prop) (a : Prop) : (a \/ b) = (term390 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3493260 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_36796 : A) : (term387 A u s _36796) = (term391 A s u _36796).
Proof. exact (@lem3493259 (term317 A s _36796) (u _36796)). Qed.
Lemma lem3493262 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493263 {A : Type'} (s : A -> Prop) (_36796 : A) : (term392 A s _36796) = (s _36796).
Proof. exact (@lem3493262 (s _36796)). Qed.
Lemma lem3493264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3493265 {A : Type'} (s : A -> Prop) (_36796 : A) : (term393 A s _36796) = (term84 A s _36796).
Proof. exact (MK_COMB (@lem3493264) (@lem3493263 A s _36796)). Qed.
Lemma lem3493266 {A : Type'} (u : A -> Prop) (_36796 : A) : (u _36796) = (u _36796).
Proof. exact (eq_refl (u _36796)). Qed.
Lemma lem3493267 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_36796 : A) : (term391 A s u _36796) = (term86 A s u _36796).
Proof. exact (MK_COMB (@lem3493265 A s _36796) (@lem3493266 A u _36796)). Qed.
Lemma lem3493268 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_36796 : A) : (term387 A u s _36796) = (term86 A s u _36796).
Proof. exact (TRANS (@lem3493260 A s u _36796) (@lem3493267 A s u _36796)). Qed.
Lemma lem3493271 {A B : Type'} (_36796 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term86 A s u _36796.
Proof. exact (EQ_MP (@lem3493268 A s u _36796) (@lem3493257 A B _36796 f t s u h1)). Qed.
Lemma lem3493272 {A B : Type'} (_36796 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term86 A s u _36796.
Proof. exact (@lem3493271 A B _36796 f t s u h1). Qed.
Lemma lem3493273 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term86 A s u x'.
Proof. exact (@lem3493272 A B x' f t s u h1). Qed.
Lemma lem3493276 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : u x'.
Proof. exact (@lem3493273 A B x' f t s u h2 (@lem3493228 A B s x' x f t x'' h1)). Qed.
Lemma lem3493277 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : term378 A u x'.
Proof. exact (fun h0 : term317 A u x' => @lem3493276 A B x' x x'' f t s u h1 h2). Qed.
Lemma lem3493279 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493280 {A : Type'} (u : A -> Prop) (x' : A) : (term378 A u x') = (u x').
Proof. exact (@lem3493279 (u x')). Qed.
Lemma lem3493281 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : u x'.
Proof. exact (EQ_MP (@lem3493280 A u x') (@lem3493277 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493283 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3492218 A B s x' x f t x'' h1) (@lem3491721 A B s x' x f t x'' h1)). Qed.
Lemma lem3493284 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term386 A B x' f x''.
Proof. exact (fun h0 : term357 A B x' f x'' => @lem3493283 A B s x' x f t x'' h1). Qed.
Lemma lem3493286 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493287 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term386 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3493286 ((f x') = (f x''))). Qed.
Lemma lem3493288 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3493287 A B x' f x'') (@lem3493284 A B s x' x f t x'' h1)). Qed.
Lemma lem3493290 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : t x''.
Proof. exact (proj2 (@lem3490718 A B s x' x f t x'' h1)). Qed.
Lemma lem3493291 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term378 A t x''.
Proof. exact (fun h0 : term317 A t x'' => @lem3493290 A B s x' x f t x'' h1). Qed.
Lemma lem3493293 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493294 {A : Type'} (t : A -> Prop) (x'' : A) : (term378 A t x'') = (t x'').
Proof. exact (@lem3493293 (t x'')). Qed.
Lemma lem3493295 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3493294 A t x'') (@lem3493291 A B s x' x f t x'' h1)). Qed.
Lemma lem3493311 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3493312 {A B : Type'} (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term356 A B f _36795 t _36794) = (term417 A B f _36795 t _36794).
Proof. exact (@lem3493311 (term317 A t _36795) (term357 A B _36794 f _36795) (t _36794)). Qed.
Lemma lem3493326 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3493327 {A B : Type'} (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term418 A B f _36795 t _36794) = (term419 A B t _36794 f _36795).
Proof. exact (@lem3493326 (t _36794) (term357 A B _36794 f _36795)). Qed.
Lemma lem3493335 {A : Type'} (t : A -> Prop) (_36795 : A) : (term150 A t _36795) = (term150 A t _36795).
Proof. exact (eq_refl (term150 A t _36795)). Qed.
Lemma lem3493336 {A B : Type'} (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term417 A B f _36795 t _36794) = (term420 A B t _36794 f _36795).
Proof. exact (MK_COMB (@lem3493335 A t _36795) (@lem3493327 A B t _36794 f _36795)). Qed.
Lemma lem3493340 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3493341 {A B : Type'} (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term420 A B t _36794 f _36795) = (term421 A B t _36794 f _36795).
Proof. exact (@lem3493340 (t _36794) (term317 A t _36795) (term357 A B _36794 f _36795)). Qed.
Lemma lem3493359 {A B : Type'} (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term417 A B f _36795 t _36794) = (term421 A B t _36794 f _36795).
Proof. exact (TRANS (@lem3493336 A B t _36794 f _36795) (@lem3493341 A B t _36794 f _36795)). Qed.
Lemma lem3493360 {A B : Type'} (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term356 A B f _36795 t _36794) = (term421 A B t _36794 f _36795).
Proof. exact (TRANS (@lem3493312 A B f _36795 t _36794) (@lem3493359 A B t _36794 f _36795)). Qed.
Lemma lem3493361 {A : Type'} (u : A -> Prop) (_36794 : A) : (term150 A u _36794) = (term150 A u _36794).
Proof. exact (eq_refl (term150 A u _36794)). Qed.
Lemma lem3493362 {A B : Type'} (u : A -> Prop) (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term358 A B u f _36795 t _36794) = (term422 A B u t _36794 f _36795).
Proof. exact (MK_COMB (@lem3493361 A u _36794) (@lem3493360 A B t _36794 f _36795)). Qed.
Lemma lem3493366 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3493367 {A B : Type'} (u : A -> Prop) (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term422 A B u t _36794 f _36795) = (term423 A B u t _36794 f _36795).
Proof. exact (@lem3493366 (t _36794) (term317 A u _36794) (term424 A B t _36794 f _36795)). Qed.
Lemma lem3493381 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3493382 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term425 A B u t _36794 f _36795) = (term426 A B t u _36794 f _36795).
Proof. exact (@lem3493381 (term317 A t _36795) (term317 A u _36794) (term357 A B _36794 f _36795)). Qed.
Lemma lem3493400 {A : Type'} (t : A -> Prop) (_36794 : A) : (term427 A t _36794) = (term427 A t _36794).
Proof. exact (eq_refl (term427 A t _36794)). Qed.
Lemma lem3493401 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term423 A B u t _36794 f _36795) = (term428 A B t u _36794 f _36795).
Proof. exact (MK_COMB (@lem3493400 A t _36794) (@lem3493382 A B t u _36794 f _36795)). Qed.
Lemma lem3493412 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term422 A B u t _36794 f _36795) = (term428 A B t u _36794 f _36795).
Proof. exact (TRANS (@lem3493367 A B u t _36794 f _36795) (@lem3493401 A B t u _36794 f _36795)). Qed.
Lemma lem3493413 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term358 A B u f _36795 t _36794) = (term428 A B t u _36794 f _36795).
Proof. exact (TRANS (@lem3493362 A B u t _36794 f _36795) (@lem3493412 A B t u _36794 f _36795)). Qed.
Lemma lem3493414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3493415 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term429 A B u f _36795 t _36794) = (term430 A B t u _36794 f _36795).
Proof. exact (MK_COMB (@lem3493414) (@lem3493413 A B t u _36794 f _36795)). Qed.
Lemma lem3493439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3493440 {A B : Type'} (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term140 A B _36794 f t _36795) = (term424 A B t _36794 f _36795).
Proof. exact (@lem3493439 (term317 A t _36795) (term357 A B _36794 f _36795)). Qed.
Lemma lem3493448 {A : Type'} (u : A -> Prop) (_36794 : A) : (term150 A u _36794) = (term150 A u _36794).
Proof. exact (eq_refl (term150 A u _36794)). Qed.
Lemma lem3493449 {A B : Type'} (u : A -> Prop) (t : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term324 A B u _36794 f t _36795) = (term425 A B u t _36794 f _36795).
Proof. exact (MK_COMB (@lem3493448 A u _36794) (@lem3493440 A B t _36794 f _36795)). Qed.
Lemma lem3493453 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3493454 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term425 A B u t _36794 f _36795) = (term426 A B t u _36794 f _36795).
Proof. exact (@lem3493453 (term317 A t _36795) (term317 A u _36794) (term357 A B _36794 f _36795)). Qed.
Lemma lem3493472 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term324 A B u _36794 f t _36795) = (term426 A B t u _36794 f _36795).
Proof. exact (TRANS (@lem3493449 A B u t _36794 f _36795) (@lem3493454 A B t u _36794 f _36795)). Qed.
Lemma lem3493473 {A : Type'} (t : A -> Prop) (_36794 : A) : (term427 A t _36794) = (term427 A t _36794).
Proof. exact (eq_refl (term427 A t _36794)). Qed.
Lemma lem3493474 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : (term431 A B u _36794 f t _36795) = (term428 A B t u _36794 f _36795).
Proof. exact (MK_COMB (@lem3493473 A t _36794) (@lem3493472 A B t u _36794 f _36795)). Qed.
Lemma lem3493485 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : ((term358 A B u f _36795 t _36794) = (term431 A B u _36794 f t _36795)) = ((term428 A B t u _36794 f _36795) = (term428 A B t u _36794 f _36795)).
Proof. exact (MK_COMB (@lem3493415 A B t u _36794 f _36795) (@lem3493474 A B t u _36794 f _36795)). Qed.
Lemma lem3493487 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3493488 (x : Prop) : (x = x) = True.
Proof. exact (@lem3493487 Prop x). Qed.
Lemma lem3493489 {A B : Type'} (t : A -> Prop) (u : A -> Prop) (_36794 : A) (f : A -> B) (_36795 : A) : ((term428 A B t u _36794 f _36795) = (term428 A B t u _36794 f _36795)) = True.
Proof. exact (@lem3493488 (term428 A B t u _36794 f _36795)). Qed.
Lemma lem3493490 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : ((term358 A B u f _36795 t _36794) = (term431 A B u _36794 f t _36795)) = True.
Proof. exact (TRANS (@lem3493485 A B t u _36794 f _36795) (@lem3493489 A B t u _36794 f _36795)). Qed.
Lemma lem3493491 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : True = ((term358 A B u f _36795 t _36794) = (term431 A B u _36794 f t _36795)).
Proof. exact (SYM (@lem3493490 A B u _36794 f t _36795)). Qed.
Lemma lem3493492 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term358 A B u f _36795 t _36794) = (term431 A B u _36794 f t _36795).
Proof. exact (EQ_MP (@lem3493491 A B u _36794 f t _36795) (@lem0)). Qed.
Lemma lem3493493 {A B : Type'} (_36794 : A) (_36795 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term431 A B u _36794 f t _36795.
Proof. exact (EQ_MP (@lem3493492 A B u _36794 f t _36795) (@lem3492261 A B _36795 _36794 f t s u h1)). Qed.
Lemma lem3493495 (b : Prop) (a : Prop) : (a \/ b) = (term390 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3493496 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term431 A B u _36794 f t _36795) = (term432 A B u f _36795 t _36794).
Proof. exact (@lem3493495 (term324 A B u _36794 f t _36795) (t _36794)). Qed.
Lemma lem3493498 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3493499 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term433 A B u _36794 f t _36795) = (term434 A B u _36794 f t _36795).
Proof. exact (@lem3493498 (term317 A u _36794) (term140 A B _36794 f t _36795)). Qed.
Lemma lem3493501 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493502 {A : Type'} (u : A -> Prop) (_36794 : A) : (term392 A u _36794) = (u _36794).
Proof. exact (@lem3493501 (u _36794)). Qed.
Lemma lem3493503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3493504 {A : Type'} (u : A -> Prop) (_36794 : A) : (term435 A u _36794) = (term63 A u _36794).
Proof. exact (MK_COMB (@lem3493503) (@lem3493502 A u _36794)). Qed.
Lemma lem3493506 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3493507 {A B : Type'} (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term436 A B _36794 f t _36795) = (term437 A B _36794 f t _36795).
Proof. exact (@lem3493506 (term357 A B _36794 f _36795) (term317 A t _36795)). Qed.
Lemma lem3493509 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493510 {A B : Type'} (_36794 : A) (f : A -> B) (_36795 : A) : (term438 A B _36794 f _36795) = ((f _36794) = (f _36795)).
Proof. exact (@lem3493509 ((f _36794) = (f _36795))). Qed.
Lemma lem3493511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3493512 {A B : Type'} (_36794 : A) (f : A -> B) (_36795 : A) : (term439 A B _36794 f _36795) = (term68 A B _36794 f _36795).
Proof. exact (MK_COMB (@lem3493511) (@lem3493510 A B _36794 f _36795)). Qed.
Lemma lem3493514 (a : Prop) : (term136 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3493515 {A : Type'} (t : A -> Prop) (_36795 : A) : (term392 A t _36795) = (t _36795).
Proof. exact (@lem3493514 (t _36795)). Qed.
Lemma lem3493516 {A B : Type'} (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term437 A B _36794 f t _36795) = (term70 A B _36794 f t _36795).
Proof. exact (MK_COMB (@lem3493512 A B _36794 f _36795) (@lem3493515 A t _36795)). Qed.
Lemma lem3493517 {A B : Type'} (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term436 A B _36794 f t _36795) = (term70 A B _36794 f t _36795).
Proof. exact (TRANS (@lem3493507 A B _36794 f t _36795) (@lem3493516 A B _36794 f t _36795)). Qed.
Lemma lem3493518 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term434 A B u _36794 f t _36795) = (term440 A B u _36794 f t _36795).
Proof. exact (MK_COMB (@lem3493504 A u _36794) (@lem3493517 A B _36794 f t _36795)). Qed.
Lemma lem3493519 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term433 A B u _36794 f t _36795) = (term440 A B u _36794 f t _36795).
Proof. exact (TRANS (@lem3493499 A B u _36794 f t _36795) (@lem3493518 A B u _36794 f t _36795)). Qed.
Lemma lem3493520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3493521 {A B : Type'} (u : A -> Prop) (_36794 : A) (f : A -> B) (t : A -> Prop) (_36795 : A) : (term441 A B u _36794 f t _36795) = (term442 A B u _36794 f t _36795).
Proof. exact (MK_COMB (@lem3493520) (@lem3493519 A B u _36794 f t _36795)). Qed.
Lemma lem3493522 {A : Type'} (t : A -> Prop) (_36794 : A) : (t _36794) = (t _36794).
Proof. exact (eq_refl (t _36794)). Qed.
Lemma lem3493523 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term432 A B u f _36795 t _36794) = (term443 A B u f _36795 t _36794).
Proof. exact (MK_COMB (@lem3493521 A B u _36794 f t _36795) (@lem3493522 A t _36794)). Qed.
Lemma lem3493524 {A B : Type'} (u : A -> Prop) (f : A -> B) (_36795 : A) (t : A -> Prop) (_36794 : A) : (term431 A B u _36794 f t _36795) = (term443 A B u f _36795 t _36794).
Proof. exact (TRANS (@lem3493496 A B u f _36795 t _36794) (@lem3493523 A B u f _36795 t _36794)). Qed.
Lemma lem3493526 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term70 A B x' f t x''.
Proof. exact (conj (@lem3493288 A B s x' x f t x'' h1) (@lem3493295 A B s x' x f t x'' h1)). Qed.
Lemma lem3493527 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : term440 A B u x' f t x''.
Proof. exact (conj (@lem3493281 A B x' x x'' f t s u h1 h2) (@lem3493526 A B s x' x f t x'' h1)). Qed.
Lemma lem3493529 {A B : Type'} (_36795 : A) (_36794 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term443 A B u f _36795 t _36794.
Proof. exact (EQ_MP (@lem3493524 A B u f _36795 t _36794) (@lem3493493 A B _36794 _36795 f t s u h1)). Qed.
Lemma lem3493530 {A B : Type'} (_36795 : A) (_36794 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term443 A B u f _36795 t _36794.
Proof. exact (@lem3493529 A B _36795 _36794 f t s u h1). Qed.
Lemma lem3493531 {A B : Type'} (x'' : A) (x' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term164 A B f t s u) : term443 A B u f x'' t x'.
Proof. exact (@lem3493530 A B x'' x' f t s u h1). Qed.
Lemma lem3493534 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : t x'.
Proof. exact (@lem3493531 A B x'' x' f t s u h2 (@lem3493527 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493535 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : term378 A t x'.
Proof. exact (fun h0 : term317 A t x' => @lem3493534 A B x' x x'' f t s u h1 h2). Qed.
Lemma lem3493537 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493538 {A : Type'} (t : A -> Prop) (x' : A) : (term378 A t x') = (t x').
Proof. exact (@lem3493537 (t x')). Qed.
Lemma lem3493539 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : t x'.
Proof. exact (EQ_MP (@lem3493538 A t x') (@lem3493535 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493541 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3493542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term168 A s t _36793) = (term167 A s t _36793).
Proof. exact (@lem3493541 (s _36793) (t _36793)). Qed.
Lemma lem3493543 {A B : Type'} (x' : A) (f : A -> B) (_36793 : A) : (term444 A B x' f _36793) = (term444 A B x' f _36793).
Proof. exact (eq_refl (term444 A B x' f _36793)). Qed.
Lemma lem3493544 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term367 A B x' f s t _36793) = (term445 A B x' f s t _36793).
Proof. exact (MK_COMB (@lem3493543 A B x' f _36793) (@lem3493542 A s t _36793)). Qed.
Lemma lem3493546 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3493547 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term445 A B x' f s t _36793) = (term446 A B x' f s t _36793).
Proof. exact (@lem3493546 ((f x') = (f _36793)) (term98 A s t _36793)). Qed.
Lemma lem3493548 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term367 A B x' f s t _36793) = (term446 A B x' f s t _36793).
Proof. exact (TRANS (@lem3493544 A B x' f s t _36793) (@lem3493547 A B x' f s t _36793)). Qed.
Lemma lem3493550 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3493551 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term446 A B x' f s t _36793) = (term447 A B x' f s t _36793).
Proof. exact (@lem3493550 (term448 A B x' f s t _36793)). Qed.
Lemma lem3493552 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_36793 : A) : (term367 A B x' f s t _36793) = (term447 A B x' f s t _36793).
Proof. exact (TRANS (@lem3493548 A B x' f s t _36793) (@lem3493551 A B x' f s t _36793)). Qed.
Lemma lem3493554 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : term98 A s t x'.
Proof. exact (conj (@lem3493221 A B s x' x f t x'' h1) (@lem3493539 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493555 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : term449 A B f s t x'.
Proof. exact (conj (@lem3493214 A B f x') (@lem3493554 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493557 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term447 A B x' f s t _36793.
Proof. exact (EQ_MP (@lem3493552 A B x' f s t _36793) (@lem3492206 A B _36793 s x' x f t x'' h1)). Qed.
Lemma lem3493558 {A B : Type'} (_36793 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term447 A B x' f s t _36793.
Proof. exact (@lem3493557 A B _36793 s x' x f t x'' h1). Qed.
Lemma lem3493559 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term270 A B s x' x f t x'') : term450 A B f s t x'.
Proof. exact (@lem3493558 A B x' s x' x f t x'' h1). Qed.
Lemma lem3493562 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : False.
Proof. exact (@lem3493559 A B s x' x f t x'' h1 (@lem3493555 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493563 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : term384.
Proof. exact (fun h0 : ~ False => @lem3493562 A B x' x x'' f t s u h1 h2). Qed.
Lemma lem3493565 (p : Prop) : (term377 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3493566 : term384 = False.
Proof. exact (@lem3493565 False). Qed.
Lemma lem3493568 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f t s u) : False.
Proof. exact (EQ_MP (@lem3493566) (@lem3493563 A B x' x x'' f t s u h1 h2)). Qed.
Lemma lem3493569 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term164 A B f s t u) : False.
Proof. exact (EQ_MP (@lem3493156) (@lem3493153 A B x' x x'' f s t u h1 h2)). Qed.
Lemma lem3493570 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3492614) (@lem3492611 A B x' s x f t h1 h2)). Qed.
Lemma lem3493571 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3492529) (@lem3492526 A B x' s x f t h1 h2)). Qed.
Lemma lem3493572 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3492444) (@lem3492441 A B x' s x f t h1 h2)). Qed.
Lemma lem3493573 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3492359) (@lem3492356 A B x' s x f t h1 h2)). Qed.
Lemma lem3493574 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : (term188 A B x f t) = False.
Proof. exact (prop_ext (fun h3 : term188 A B x f t => @lem3493570 A B x' s x f t h1 h2) (fun h3 : False => @lem3491105 A B x f t h1)). Qed.
Lemma lem3493575 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3493574 A B x' s x f t h1 h2) (@lem3491105 A B x f t h1)). Qed.
Lemma lem3493576 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : (term188 A B x f t) = False.
Proof. exact (prop_ext (fun h3 : term188 A B x f t => @lem3493571 A B x' s x f t h1 h2) (fun h3 : False => @lem3490988 A B x f t h1)). Qed.
Lemma lem3493577 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3493576 A B x' s x f t h1 h2) (@lem3490988 A B x f t h1)). Qed.
Lemma lem3493578 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : (term188 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term188 A B x f s => @lem3493572 A B x' s x f t h1 h2) (fun h3 : False => @lem3490871 A B x f s h1)). Qed.
Lemma lem3493579 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3493578 A B x' s x f t h1 h2) (@lem3490871 A B x f s h1)). Qed.
Lemma lem3493580 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : (term188 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term188 A B x f s => @lem3493573 A B x' s x f t h1 h2) (fun h3 : False => @lem3490754 A B x f s h1)). Qed.
Lemma lem3493581 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3493580 A B x' s x f t h1 h2) (@lem3490754 A B x f s h1)). Qed.
Lemma lem3493582 {A B : Type'} (x' : A) (x : B) (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term270 A B s x' x f t x'') (h2 : term92 A B f t s u) : False.
Proof. exact (or_elim (@lem3490564 A B f t s u h2) (fun h0 : term164 A B f s t u => @lem3493569 A B x' x x'' f s t u h1 h0) (fun h0 : term164 A B f t s u => @lem3493568 A B x' x x'' f t s u h1 h0)). Qed.
Lemma lem3493583 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A B x f t) (h2 : term217 A B x' s x f t) (h3 : term92 A B f t s u) : False.
Proof. exact (or_elim (@lem3490564 A B f t s u h3) (fun h0 : term164 A B f s t u => @lem3493577 A B x' s x f t h1 h2) (fun h0 : term164 A B f t s u => @lem3493575 A B x' s x f t h1 h2)). Qed.
Lemma lem3493584 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A B x f s) (h2 : term217 A B x' s x f t) (h3 : term92 A B f t s u) : False.
Proof. exact (or_elim (@lem3490564 A B f t s u h3) (fun h0 : term164 A B f s t u => @lem3493581 A B x' s x f t h1 h2) (fun h0 : term164 A B f t s u => @lem3493579 A B x' s x f t h1 h2)). Qed.
Lemma lem3493585 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term217 A B x' s x f t) (h2 : term92 A B f t s u) : False.
Proof. exact (or_elim (@lem3490696 A B x' s x f t h1) (fun h0 : term188 A B x f s => @lem3493584 A B x' x f t s u h0 h1 h2) (fun h0 : term188 A B x f t => @lem3493583 A B x' x f t s u h0 h1 h2)). Qed.
Lemma lem3493586 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term92 A B f t s u) (h2 : term307 A B s x' x f t x'') : False.
Proof. exact (or_elim (@lem3490693 A B s x' x f t x'' h2) (fun h0 : term217 A B x' s x f t => @lem3493585 A B x' x f t s u h0 h1) (fun h0 : term270 A B s x' x f t x'' => @lem3493582 A B x' x x'' f t s u h0 h1)). Qed.
Lemma lem3493587 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term92 A B f t s u) (h2 : term307 A B s x' x f t x'') : (term307 A B s x' x f t x'') = False.
Proof. exact (prop_ext (fun h3 : term307 A B s x' x f t x'' => @lem3493586 A B u s x' x f t x'' h1 h2) (fun h3 : False => @lem3490693 A B s x' x f t x'' h2)). Qed.
Lemma lem3493588 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term92 A B f t s u) (h2 : term307 A B s x' x f t x'') : False.
Proof. exact (EQ_MP (@lem3493587 A B u s x' x f t x'' h1 h2) (@lem3490693 A B s x' x f t x'' h2)). Qed.
Lemma lem3493589 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term310 A B s x' x f t) (h2 : term92 A B f t s u) : False.
Proof. exact (ex_elim (@lem3490447 A B s x' x f t h1) (fun x'' : A => fun h0 : term309 A B s x' x f t x'' => @lem3493588 A B u s x' x f t x'' h2 h0)). Qed.
Lemma lem3493590 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term138 A B s x f t) (h2 : term92 A B f t s u) : False.
Proof. exact (ex_elim (@lem3490446 A B s x f t h1) (fun x' : A => fun h0 : term311 A B s x f t x' => @lem3493589 A B x' x f t s u h0 h2)). Qed.
Lemma lem3493591 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term138 A B s x f t) (h2 : term92 A B f t s u) : (term138 A B s x f t) = False.
Proof. exact (prop_ext (fun h3 : term138 A B s x f t => @lem3493590 A B x f t s u h1 h2) (fun h3 : False => @lem3489586 A B s x f t h1)). Qed.
Lemma lem3493592 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term138 A B s x f t) (h2 : term92 A B f t s u) : False.
Proof. exact (EQ_MP (@lem3493591 A B x f t s u h1 h2) (@lem3489586 A B s x f t h1)). Qed.
Lemma lem3493593 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term92 A B f t s u) : term137 A B s x f t.
Proof. exact (fun h0 : term138 A B s x f t => @lem3493592 A B x f t s u h0 h1). Qed.
Lemma lem3493594 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term92 A B f t s u) : (term104 A B x f s t) = (term116 A B s x f t).
Proof. exact (EQ_MP (@lem3489585 A B s x f t) (@lem3493593 A B x f t s u h1)). Qed.
Lemma lem3493599 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term92 A B f t s u) : term119 A B s f t.
Proof. exact (fun x : B => @lem3493594 A B x f t s u h1). Qed.
Lemma lem3493600 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : term120 A B u s f t.
Proof. exact (fun h0 : term92 A B f t s u => @lem3493599 A B f t s u h0). Qed.
Lemma lem3493605 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : term122 A B s f t.
Proof. exact (fun u : A -> Prop => @lem3493600 A B u s f t). Qed.
Lemma lem3493610 {A B : Type'} (s : A -> Prop) (f : A -> B) : term124 A B s f.
Proof. exact (fun t : A -> Prop => @lem3493605 A B s f t). Qed.
Lemma lem3493615 {A B : Type'} (f : A -> B) : term126 A B f.
Proof. exact (fun s : A -> Prop => @lem3493610 A B s f). Qed.
Lemma lem3493620 {A B : Type'} : term128 A B.
Proof. exact (fun f : A -> B => @lem3493615 A B f). Qed.
Lemma lem3493621 {A B : Type'} : term130 A B.
Proof. exact (EQ_MP (@lem3489580 A B) (@lem3493620 A B)). Qed.
Lemma lem3493623 {A B : Type'} : term130 A B.
Proof. exact (@lem3489086 A B (@lem3493621 A B)). Qed.
Lemma lem3493624 {A B : Type'} (h1 : term131 A B) : False.
Proof. exact (@lem3493623 A B (@lem3489070 A B h1)). Qed.
Lemma lem3493625 {A B : Type'} (h1 : term131 A B) : (term131 A B) = False.
Proof. exact (prop_ext (fun h2 : term131 A B => @lem3493624 A B h1) (fun h2 : False => @lem3489070 A B h1)). Qed.
Lemma lem3493626 {A B : Type'} (h1 : term131 A B) : False.
Proof. exact (EQ_MP (@lem3493625 A B h1) (@lem3489070 A B h1)). Qed.
Lemma lem3493627 {A B : Type'} : term130 A B.
Proof. exact (fun h0 : term131 A B => @lem3493626 A B h0). Qed.
Lemma lem3493628 {A B : Type'} : term128 A B.
Proof. exact (EQ_MP (@lem3489069 A B) (@lem3493627 A B)). Qed.
Lemma lem3493629 {A B : Type'} : term42 A B.
Proof. exact (EQ_MP (@lem3489065 A B) (@lem3493628 A B)). Qed.
Lemma lem3493630 {A B : Type'} : term41 A B.
Proof. exact (EQ_MP (@lem3488643 A B) (@lem3493629 A B)). Qed.
