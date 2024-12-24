Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_UNION_OVERLAP_term_abbrevs.
Require Import CARD_UNION_OVERLAP_EQ_spec.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3969605 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) (h1 : ((term0 _101466 s t) = (term1 _101466 s t)) = ((@INTER _101466 s t) = (@EMPTY _101466))) : ((term0 _101466 s t) = (term1 _101466 s t)) = ((@INTER _101466 s t) = (@EMPTY _101466)).
Proof. exact (h1). Qed.
Lemma lem3969606 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) (h1 : ((term0 _101466 s t) = (term1 _101466 s t)) = ((@INTER _101466 s t) = (@EMPTY _101466))) : ((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t)).
Proof. exact (SYM (@lem3969605 _101466 s t h1)). Qed.
Lemma lem3969607 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) (h1 : ((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t))) : ((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t)).
Proof. exact (h1). Qed.
Lemma lem3969608 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) (h1 : ((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t))) : ((term0 _101466 s t) = (term1 _101466 s t)) = ((@INTER _101466 s t) = (@EMPTY _101466)).
Proof. exact (SYM (@lem3969607 _101466 s t h1)). Qed.
Lemma lem3969609 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : (((term0 _101466 s t) = (term1 _101466 s t)) = ((@INTER _101466 s t) = (@EMPTY _101466))) = (((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t))).
Proof. exact (prop_ext (fun h1 : ((term0 _101466 s t) = (term1 _101466 s t)) = ((@INTER _101466 s t) = (@EMPTY _101466)) => @lem3969606 _101466 s t h1) (fun h1 : ((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t)) => @lem3969608 _101466 s t h1)). Qed.
Lemma lem3969610 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : (term2 _101466 s t) = (term2 _101466 s t).
Proof. exact (eq_refl (term2 _101466 s t)). Qed.
Lemma lem3969611 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : (term3 _101466 s t) = (term4 _101466 s t).
Proof. exact (MK_COMB (@lem3969610 _101466 s t) (@lem3969609 _101466 s t)). Qed.
Lemma lem3969612 {_101466 : Type'} (s : _101466 -> Prop) : (term5 _101466 s) = (term6 _101466 s).
Proof. exact (fun_ext (fun t : _101466 -> Prop => @lem3969611 _101466 s t)). Qed.
Lemma lem3969613 {_101466 : Type'} : (@all (_101466 -> Prop)) = (@all (_101466 -> Prop)).
Proof. exact (eq_refl (@all (_101466 -> Prop))). Qed.
Lemma lem3969614 {_101466 : Type'} (s : _101466 -> Prop) : (term7 _101466 s) = (term8 _101466 s).
Proof. exact (MK_COMB (@lem3969613 _101466) (@lem3969612 _101466 s)). Qed.
Lemma lem3969615 {_101466 : Type'} : (term9 _101466) = (term10 _101466).
Proof. exact (fun_ext (fun s : _101466 -> Prop => @lem3969614 _101466 s)). Qed.
Lemma lem3969616 {_101466 : Type'} : (@all (_101466 -> Prop)) = (@all (_101466 -> Prop)).
Proof. exact (eq_refl (@all (_101466 -> Prop))). Qed.
Lemma lem3969617 {_101466 : Type'} : (term11 _101466) = (term12 _101466).
Proof. exact (MK_COMB (@lem3969616 _101466) (@lem3969615 _101466)). Qed.
Lemma lem3969618 {_101466 : Type'} : term12 _101466.
Proof. exact (EQ_MP (@lem3969617 _101466) (@lem3969598 _101466)). Qed.
Lemma lem3969619 {_101466 : Type'} (s : _101466 -> Prop) : term13 _101466 s.
Proof. exact (@lem3969618 _101466 s). Qed.
Lemma lem3969620 {_101466 : Type'} (s : _101466 -> Prop) : (term13 _101466 s) = (term8 _101466 s).
Proof. exact (eq_refl (term13 _101466 s)). Qed.
Lemma lem3969621 {_101466 : Type'} (s : _101466 -> Prop) : term8 _101466 s.
Proof. exact (EQ_MP (@lem3969620 _101466 s) (@lem3969619 _101466 s)). Qed.
Lemma lem3969622 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : term14 _101466 s t.
Proof. exact (@lem3969621 _101466 s t). Qed.
Lemma lem3969623 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : (term14 _101466 s t) = (term4 _101466 s t).
Proof. exact (eq_refl (term14 _101466 s t)). Qed.
Lemma lem3969624 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : term4 _101466 s t.
Proof. exact (EQ_MP (@lem3969623 _101466 s t) (@lem3969622 _101466 s t)). Qed.
Lemma lem3969625 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) (h1 : term15 _101466 s t) : term15 _101466 s t.
Proof. exact (h1). Qed.
Lemma lem3969626 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) (h1 : term15 _101466 s t) : ((@INTER _101466 s t) = (@EMPTY _101466)) = ((term0 _101466 s t) = (term1 _101466 s t)).
Proof. exact (@lem3969624 _101466 s t (@lem3969625 _101466 s t h1)). Qed.
Lemma lem3969643 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3969644 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem3969643 p q p' q'). Qed.
Lemma lem3969645 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem3969644 p q p'). Qed.
Lemma lem3969646 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term19 _101508 s t.
Proof. exact (@lem3969645 (term20 _101508 s t) (term21 _101508 s t)). Qed.
Lemma lem3969647 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (p' : Prop) : term22 _101508 s t p'.
Proof. exact (@lem3969646 _101508 s t p'). Qed.
Lemma lem3969648 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (p' : Prop) : (term22 _101508 s t p') = (term23 _101508 s t p').
Proof. exact (eq_refl (term22 _101508 s t p')). Qed.
Lemma lem3969649 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (p' : Prop) : term23 _101508 s t p'.
Proof. exact (EQ_MP (@lem3969648 _101508 s t p') (@lem3969647 _101508 s t p')). Qed.
Lemma lem3969650 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (p' : Prop) (q' : Prop) : term24 _101508 s t p' q'.
Proof. exact (@lem3969649 _101508 s t p' q'). Qed.
Lemma lem3969651 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (p' : Prop) (q' : Prop) : (term24 _101508 s t p' q') = (term25 _101508 s t p' q').
Proof. exact (eq_refl (term24 _101508 s t p' q')). Qed.
Lemma lem3969652 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (p' : Prop) (q' : Prop) : term25 _101508 s t p' q'.
Proof. exact (EQ_MP (@lem3969651 _101508 s t p' q') (@lem3969650 _101508 s t p' q')). Qed.
Lemma lem3969657 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term20 _101508 s t) = (term20 _101508 s t).
Proof. exact (eq_refl (term20 _101508 s t)). Qed.
Lemma lem3969658 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (q' : Prop) : term26 _101508 s t q'.
Proof. exact (@lem3969652 _101508 s t (term20 _101508 s t) q'). Qed.
Lemma lem3969659 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (q' : Prop) : term27 _101508 s t q'.
Proof. exact (@lem3969658 _101508 s t q' (@lem3969657 _101508 s t)). Qed.
Lemma lem3969660 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : term20 _101508 s t.
Proof. exact (h1). Qed.
Lemma lem3969661 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : term28 _101508 s t.
Proof. exact (proj2 (@lem3969660 _101508 s t h1)). Qed.
Lemma lem3969665 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : @FINITE _101508 t.
Proof. exact (proj1 (@lem3969661 _101508 s t h1)). Qed.
Lemma lem3969666 {_101508 : Type'} (t : _101508 -> Prop) : (@FINITE _101508 t) = ((@FINITE _101508 t) = True).
Proof. exact (@lem7 (@FINITE _101508 t)). Qed.
Lemma lem3969668 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : @FINITE _101508 s.
Proof. exact (proj1 (@lem3969660 _101508 s t h1)). Qed.
Lemma lem3969669 {_101508 : Type'} (s : _101508 -> Prop) : (@FINITE _101508 s) = ((@FINITE _101508 s) = True).
Proof. exact (@lem7 (@FINITE _101508 s)). Qed.
Lemma lem3969672 {_101466 : Type'} (s : _101466 -> Prop) (t : _101466 -> Prop) : term4 _101466 s t.
Proof. exact (fun h0 : term15 _101466 s t => @lem3969626 _101466 s t h0). Qed.
Lemma lem3969673 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term4 _101508 s t.
Proof. exact (@lem3969672 _101508 s t). Qed.
Lemma lem3969677 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : (@FINITE _101508 s) = True.
Proof. exact (EQ_MP (@lem3969669 _101508 s) (@lem3969668 _101508 s t h1)). Qed.
Lemma lem3969678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3969679 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : (term29 _101508 s) = (and True).
Proof. exact (MK_COMB (@lem3969678) (@lem3969677 _101508 s t h1)). Qed.
Lemma lem3969681 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : (@FINITE _101508 t) = True.
Proof. exact (EQ_MP (@lem3969666 _101508 t) (@lem3969665 _101508 s t h1)). Qed.
Lemma lem3969682 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : (term15 _101508 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3969679 _101508 s t h1) (@lem3969681 _101508 s t h1)). Qed.
Lemma lem3969684 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3969685 : (True /\ True) = True.
Proof. exact (@lem3969684 True). Qed.
Lemma lem3969686 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : (term15 _101508 s t) = True.
Proof. exact (TRANS (@lem3969682 _101508 s t h1) (@lem3969685)). Qed.
Lemma lem3969687 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : True = (term15 _101508 s t).
Proof. exact (SYM (@lem3969686 _101508 s t h1)). Qed.
Lemma lem3969688 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : term15 _101508 s t.
Proof. exact (EQ_MP (@lem3969687 _101508 s t h1) (@lem0)). Qed.
Lemma lem3969689 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : ((@INTER _101508 s t) = (@EMPTY _101508)) = ((term0 _101508 s t) = (term1 _101508 s t)).
Proof. exact (@lem3969673 _101508 s t (@lem3969688 _101508 s t h1)). Qed.
Lemma lem3969692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3969693 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (h1 : term20 _101508 s t) : (term21 _101508 s t) = (term30 _101508 s t).
Proof. exact (MK_COMB (@lem3969692) (@lem3969689 _101508 s t h1)). Qed.
Lemma lem3969696 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term31 _101508 s t.
Proof. exact (fun h0 : term20 _101508 s t => @lem3969693 _101508 s t h0). Qed.
Lemma lem3969697 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term32 _101508 s t.
Proof. exact (@lem3969659 _101508 s t (term30 _101508 s t)). Qed.
Lemma lem3969698 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term33 _101508 s t) = (term34 _101508 s t).
Proof. exact (@lem3969697 _101508 s t (@lem3969696 _101508 s t)). Qed.
Lemma lem3969742 {_101508 : Type'} (s : _101508 -> Prop) : (term35 _101508 s) = (term36 _101508 s).
Proof. exact (fun_ext (fun t : _101508 -> Prop => @lem3969698 _101508 s t)). Qed.
Lemma lem3969786 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3969787 {_101508 : Type'} (s : _101508 -> Prop) : (term37 _101508 s) = (term38 _101508 s).
Proof. exact (MK_COMB (@lem3969786 _101508) (@lem3969742 _101508 s)). Qed.
Lemma lem3969835 {_101508 : Type'} : (term39 _101508) = (term40 _101508).
Proof. exact (fun_ext (fun s : _101508 -> Prop => @lem3969787 _101508 s)). Qed.
Lemma lem3969883 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3969884 {_101508 : Type'} : (term41 _101508) = (term42 _101508).
Proof. exact (MK_COMB (@lem3969883 _101508) (@lem3969835 _101508)). Qed.
Lemma lem3969936 {_101508 : Type'} : (term42 _101508) = (term41 _101508).
Proof. exact (SYM (@lem3969884 _101508)). Qed.
Lemma lem3969968 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term34 _101508 s t) = (term34 _101508 s t).
Proof. exact (eq_refl (term34 _101508 s t)). Qed.
Lemma lem3969969 {_101508 : Type'} (s : _101508 -> Prop) : (term36 _101508 s) = (term36 _101508 s).
Proof. exact (fun_ext (fun t : _101508 -> Prop => @lem3969968 _101508 s t)). Qed.
Lemma lem3969970 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3969971 {_101508 : Type'} (s : _101508 -> Prop) : (term38 _101508 s) = (term38 _101508 s).
Proof. exact (MK_COMB (@lem3969970 _101508) (@lem3969969 _101508 s)). Qed.
Lemma lem3969972 {_101508 : Type'} : (term40 _101508) = (term40 _101508).
Proof. exact (fun_ext (fun s : _101508 -> Prop => @lem3969971 _101508 s)). Qed.
Lemma lem3969973 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3969975 {_101508 : Type'} : (term42 _101508) = (term42 _101508).
Proof. exact (MK_COMB (@lem3969973 _101508) (@lem3969972 _101508)). Qed.
Lemma lem3969983 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term43 _101508 s t) = (term44 _101508 s t).
Proof. exact (@lem17045 (@FINITE _101508 t) (term45 _101508 s t)). Qed.
Lemma lem3969985 {_101508 : Type'} (s : _101508 -> Prop) : (term46 _101508 s) = (term46 _101508 s).
Proof. exact (eq_refl (term46 _101508 s)). Qed.
Lemma lem3969986 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term47 _101508 s t) = (term48 _101508 s t).
Proof. exact (MK_COMB (@lem3969985 _101508 s) (@lem3969983 _101508 s t)). Qed.
Lemma lem3969987 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term49 _101508 s t) = (term47 _101508 s t).
Proof. exact (@lem17045 (@FINITE _101508 s) (term28 _101508 s t)). Qed.
Lemma lem3969988 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term49 _101508 s t) = (term48 _101508 s t).
Proof. exact (TRANS (@lem3969987 _101508 s t) (@lem3969986 _101508 s t)). Qed.
Lemma lem3969989 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term30 _101508 s t) = (term30 _101508 s t).
Proof. exact (eq_refl (term30 _101508 s t)). Qed.
Lemma lem3969990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3969991 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term50 _101508 s t) = (term51 _101508 s t).
Proof. exact (MK_COMB (@lem3969990) (@lem3969988 _101508 s t)). Qed.
Lemma lem3969992 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term52 _101508 s t) = (term53 _101508 s t).
Proof. exact (MK_COMB (@lem3969991 _101508 s t) (@lem3969989 _101508 s t)). Qed.
Lemma lem3969993 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term34 _101508 s t) = (term52 _101508 s t).
Proof. exact (@lem17265 (term20 _101508 s t) (term30 _101508 s t)). Qed.
Lemma lem3969994 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term34 _101508 s t) = (term53 _101508 s t).
Proof. exact (TRANS (@lem3969993 _101508 s t) (@lem3969992 _101508 s t)). Qed.
Lemma lem3969995 {_101508 : Type'} (s : _101508 -> Prop) : (term36 _101508 s) = (term54 _101508 s).
Proof. exact (fun_ext (fun t : _101508 -> Prop => @lem3969994 _101508 s t)). Qed.
Lemma lem3969996 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3969997 {_101508 : Type'} (s : _101508 -> Prop) : (term38 _101508 s) = (term55 _101508 s).
Proof. exact (MK_COMB (@lem3969996 _101508) (@lem3969995 _101508 s)). Qed.
Lemma lem3969998 {_101508 : Type'} : (term40 _101508) = (term56 _101508).
Proof. exact (fun_ext (fun s : _101508 -> Prop => @lem3969997 _101508 s)). Qed.
Lemma lem3969999 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970000 {_101508 : Type'} : (term42 _101508) = (term57 _101508).
Proof. exact (MK_COMB (@lem3969999 _101508) (@lem3969998 _101508)). Qed.
Lemma lem3970001 {_101508 : Type'} : (term42 _101508) = (term57 _101508).
Proof. exact (TRANS (@lem3969975 _101508) (@lem3970000 _101508)). Qed.
Lemma lem3970002 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term53 _101508 s t) = (term53 _101508 s t).
Proof. exact (eq_refl (term53 _101508 s t)). Qed.
Lemma lem3970003 {_101508 : Type'} (s : _101508 -> Prop) : (term54 _101508 s) = (term54 _101508 s).
Proof. exact (fun_ext (fun t : _101508 -> Prop => @lem3970002 _101508 s t)). Qed.
Lemma lem3970004 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970005 {_101508 : Type'} (s : _101508 -> Prop) : (term55 _101508 s) = (term55 _101508 s).
Proof. exact (MK_COMB (@lem3970004 _101508) (@lem3970003 _101508 s)). Qed.
Lemma lem3970006 {_101508 : Type'} : (term56 _101508) = (term56 _101508).
Proof. exact (fun_ext (fun s : _101508 -> Prop => @lem3970005 _101508 s)). Qed.
Lemma lem3970007 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970008 {_101508 : Type'} : (term57 _101508) = (term57 _101508).
Proof. exact (MK_COMB (@lem3970007 _101508) (@lem3970006 _101508)). Qed.
Lemma lem3970031 {_101508 : Type'} : (term42 _101508) = (term57 _101508).
Proof. exact (TRANS (@lem3970001 _101508) (@lem3970008 _101508)). Qed.
Lemma lem3970072 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term53 _101508 s t) = (term53 _101508 s t).
Proof. exact (eq_refl (term53 _101508 s t)). Qed.
Lemma lem3970073 {_101508 : Type'} (s : _101508 -> Prop) : (term54 _101508 s) = (term54 _101508 s).
Proof. exact (fun_ext (fun t : _101508 -> Prop => @lem3970072 _101508 s t)). Qed.
Lemma lem3970074 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970075 {_101508 : Type'} (s : _101508 -> Prop) : (term55 _101508 s) = (term55 _101508 s).
Proof. exact (MK_COMB (@lem3970074 _101508) (@lem3970073 _101508 s)). Qed.
Lemma lem3970076 {_101508 : Type'} : (term56 _101508) = (term56 _101508).
Proof. exact (fun_ext (fun s : _101508 -> Prop => @lem3970075 _101508 s)). Qed.
Lemma lem3970077 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970078 {_101508 : Type'} : (term57 _101508) = (term57 _101508).
Proof. exact (MK_COMB (@lem3970077 _101508) (@lem3970076 _101508)). Qed.
Lemma lem3970081 {_101508 : Type'} : (term42 _101508) = (term57 _101508).
Proof. exact (TRANS (@lem3970031 _101508) (@lem3970078 _101508)). Qed.
Lemma lem3970083 (m : nat) (n : nat) : (Peano.lt m n) = (term58 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3970084 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term45 _101508 s t) = (term59 _101508 s t).
Proof. exact (@lem3970083 (term0 _101508 s t) (term1 _101508 s t)). Qed.
Lemma lem3970086 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3970087 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term62 _101508 s t) = (term63 _101508 s t).
Proof. exact (@lem3970086 (@CARD _101508 s) (@CARD _101508 t)). Qed.
Lemma lem3970088 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term64 _101508 s t) = (term64 _101508 s t).
Proof. exact (eq_refl (term64 _101508 s t)). Qed.
Lemma lem3970089 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term59 _101508 s t) = (term65 _101508 s t).
Proof. exact (MK_COMB (@lem3970088 _101508 s t) (@lem3970087 _101508 s t)). Qed.
Lemma lem3970090 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term45 _101508 s t) = (term65 _101508 s t).
Proof. exact (TRANS (@lem3970084 _101508 s t) (@lem3970089 _101508 s t)). Qed.
Lemma lem3970091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3970092 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term66 _101508 s t) = (term67 _101508 s t).
Proof. exact (MK_COMB (@lem3970091) (@lem3970090 _101508 s t)). Qed.
Lemma lem3970093 {_101508 : Type'} (t : _101508 -> Prop) : (term46 _101508 t) = (term46 _101508 t).
Proof. exact (eq_refl (term46 _101508 t)). Qed.
Lemma lem3970094 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term44 _101508 s t) = (term68 _101508 s t).
Proof. exact (MK_COMB (@lem3970093 _101508 t) (@lem3970092 _101508 s t)). Qed.
Lemma lem3970095 {_101508 : Type'} (s : _101508 -> Prop) : (term46 _101508 s) = (term46 _101508 s).
Proof. exact (eq_refl (term46 _101508 s)). Qed.
Lemma lem3970096 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term48 _101508 s t) = (term69 _101508 s t).
Proof. exact (MK_COMB (@lem3970095 _101508 s) (@lem3970094 _101508 s t)). Qed.
Lemma lem3970097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3970098 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term51 _101508 s t) = (term70 _101508 s t).
Proof. exact (MK_COMB (@lem3970097) (@lem3970096 _101508 s t)). Qed.
Lemma lem3970100 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3970101 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : ((term0 _101508 s t) = (term1 _101508 s t)) = ((term71 _101508 s t) = (term62 _101508 s t)).
Proof. exact (@lem3970100 (term0 _101508 s t) (term1 _101508 s t)). Qed.
Lemma lem3970105 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3970106 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term62 _101508 s t) = (term63 _101508 s t).
Proof. exact (@lem3970105 (@CARD _101508 s) (@CARD _101508 t)). Qed.
Lemma lem3970107 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term72 _101508 s t) = (term72 _101508 s t).
Proof. exact (eq_refl (term72 _101508 s t)). Qed.
Lemma lem3970108 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : ((term71 _101508 s t) = (term62 _101508 s t)) = ((term71 _101508 s t) = (term63 _101508 s t)).
Proof. exact (MK_COMB (@lem3970107 _101508 s t) (@lem3970106 _101508 s t)). Qed.
Lemma lem3970109 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : ((term0 _101508 s t) = (term1 _101508 s t)) = ((term71 _101508 s t) = (term63 _101508 s t)).
Proof. exact (TRANS (@lem3970101 _101508 s t) (@lem3970108 _101508 s t)). Qed.
Lemma lem3970110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3970111 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term30 _101508 s t) = (term73 _101508 s t).
Proof. exact (MK_COMB (@lem3970110) (@lem3970109 _101508 s t)). Qed.
Lemma lem3970112 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term53 _101508 s t) = (term74 _101508 s t).
Proof. exact (MK_COMB (@lem3970098 _101508 s t) (@lem3970111 _101508 s t)). Qed.
Lemma lem3970113 {_101508 : Type'} (s : _101508 -> Prop) : (term54 _101508 s) = (term75 _101508 s).
Proof. exact (fun_ext (fun t : _101508 -> Prop => @lem3970112 _101508 s t)). Qed.
Lemma lem3970114 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970115 {_101508 : Type'} (s : _101508 -> Prop) : (term55 _101508 s) = (term76 _101508 s).
Proof. exact (MK_COMB (@lem3970114 _101508) (@lem3970113 _101508 s)). Qed.
Lemma lem3970116 {_101508 : Type'} : (term56 _101508) = (term77 _101508).
Proof. exact (fun_ext (fun s : _101508 -> Prop => @lem3970115 _101508 s)). Qed.
Lemma lem3970117 {_101508 : Type'} : (@all (_101508 -> Prop)) = (@all (_101508 -> Prop)).
Proof. exact (eq_refl (@all (_101508 -> Prop))). Qed.
Lemma lem3970118 {_101508 : Type'} : (term57 _101508) = (term78 _101508).
Proof. exact (MK_COMB (@lem3970117 _101508) (@lem3970116 _101508)). Qed.
Lemma lem3970119 {_101508 : Type'} : (term42 _101508) = (term78 _101508).
Proof. exact (TRANS (@lem3970081 _101508) (@lem3970118 _101508)). Qed.
Lemma lem3970120 {_101508 : Type'} (s : _101508 -> Prop) : term79 _101508 s.
Proof. exact (@lem2307535 (@CARD _101508 s)). Qed.
Lemma lem3970121 {_101508 : Type'} (s : _101508 -> Prop) : (term79 _101508 s) = (term80 _101508 s).
Proof. exact (eq_refl (term79 _101508 s)). Qed.
Lemma lem3970122 {_101508 : Type'} (s : _101508 -> Prop) : term80 _101508 s.
Proof. exact (EQ_MP (@lem3970121 _101508 s) (@lem3970120 _101508 s)). Qed.
Lemma lem3970123 {_101508 : Type'} (t : _101508 -> Prop) : term79 _101508 t.
Proof. exact (@lem2307535 (@CARD _101508 t)). Qed.
Lemma lem3970124 {_101508 : Type'} (t : _101508 -> Prop) : (term79 _101508 t) = (term80 _101508 t).
Proof. exact (eq_refl (term79 _101508 t)). Qed.
Lemma lem3970125 {_101508 : Type'} (t : _101508 -> Prop) : term80 _101508 t.
Proof. exact (EQ_MP (@lem3970124 _101508 t) (@lem3970123 _101508 t)). Qed.
Lemma lem3970126 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term81 _101508 s t.
Proof. exact (@lem2307535 (term0 _101508 s t)). Qed.
Lemma lem3970127 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : (term81 _101508 s t) = (term82 _101508 s t).
Proof. exact (eq_refl (term81 _101508 s t)). Qed.
Lemma lem3970128 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term82 _101508 s t.
Proof. exact (EQ_MP (@lem3970127 _101508 s t) (@lem3970126 _101508 s t)). Qed.
Lemma lem3970129 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term83 _101508 s t _45802 _45800 _45801) = (term84 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem2318604 (term84 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970152 {_101508 : Type'} (s : _101508 -> Prop) : (term85 _101508 s) = (@FINITE _101508 s).
Proof. exact (@lem16933 (@FINITE _101508 s)). Qed.
Lemma lem3970155 {_101508 : Type'} (t : _101508 -> Prop) : (term85 _101508 t) = (@FINITE _101508 t).
Proof. exact (@lem16933 (@FINITE _101508 t)). Qed.
Lemma lem3970158 (_45802 : int) (_45800 : int) (_45801 : int) : (term86 _45802 _45800 _45801) = (term87 _45802 _45800 _45801).
Proof. exact (@lem16933 (term87 _45802 _45800 _45801)). Qed.
Lemma lem3970159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970160 {_101508 : Type'} (t : _101508 -> Prop) : (term88 _101508 t) = (term29 _101508 t).
Proof. exact (MK_COMB (@lem3970159) (@lem3970155 _101508 t)). Qed.
Lemma lem3970161 {_101508 : Type'} (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term89 _101508 t _45802 _45800 _45801) = (term90 _101508 t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970160 _101508 t) (@lem3970158 _45802 _45800 _45801)). Qed.
Lemma lem3970162 {_101508 : Type'} (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term91 _101508 t _45802 _45800 _45801) = (term89 _101508 t _45802 _45800 _45801).
Proof. exact (@lem17160 (term92 _101508 t) (term93 _45802 _45800 _45801)). Qed.
Lemma lem3970163 {_101508 : Type'} (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term91 _101508 t _45802 _45800 _45801) = (term90 _101508 t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970162 _101508 t _45802 _45800 _45801) (@lem3970161 _101508 t _45802 _45800 _45801)). Qed.
Lemma lem3970164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970165 {_101508 : Type'} (s : _101508 -> Prop) : (term88 _101508 s) = (term29 _101508 s).
Proof. exact (MK_COMB (@lem3970164) (@lem3970152 _101508 s)). Qed.
Lemma lem3970166 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term94 _101508 s t _45802 _45800 _45801) = (term95 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970165 _101508 s) (@lem3970163 _101508 t _45802 _45800 _45801)). Qed.
Lemma lem3970167 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term96 _101508 s t _45802 _45800 _45801) = (term94 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem17160 (term92 _101508 s) (term97 _101508 t _45802 _45800 _45801)). Qed.
Lemma lem3970168 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term96 _101508 s t _45802 _45800 _45801) = (term95 _101508 s t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970167 _101508 s t _45802 _45800 _45801) (@lem3970166 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970171 (_45802 : int) (_45800 : int) (_45801 : int) : (term98 _45802 _45800 _45801) = (_45802 = (int_add _45800 _45801)).
Proof. exact (@lem16933 (_45802 = (int_add _45800 _45801))). Qed.
Lemma lem3970172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970173 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term99 _101508 s t _45802 _45800 _45801) = (term100 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970172) (@lem3970168 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970174 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term101 _101508 s t _45802 _45800 _45801) = (term102 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970173 _101508 s t _45802 _45800 _45801) (@lem3970171 _45802 _45800 _45801)). Qed.
Lemma lem3970175 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term103 _101508 s t _45802 _45800 _45801) = (term101 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem17160 (term104 _101508 s t _45802 _45800 _45801) (term105 _45802 _45800 _45801)). Qed.
Lemma lem3970176 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term103 _101508 s t _45802 _45800 _45801) = (term102 _101508 s t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970175 _101508 s t _45802 _45800 _45801) (@lem3970174 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970178 (_45802 : int) : (term106 _45802) = (term106 _45802).
Proof. exact (eq_refl (term106 _45802)). Qed.
Lemma lem3970179 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term107 _101508 s t _45802 _45800 _45801) = (term108 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970178 _45802) (@lem3970176 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970180 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term109 _101508 s t _45802 _45800 _45801) = (term107 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem17362 (term110 _45802) (term111 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970181 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term109 _101508 s t _45802 _45800 _45801) = (term108 _101508 s t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970180 _101508 s t _45802 _45800 _45801) (@lem3970179 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970183 (_45801 : int) : (term106 _45801) = (term106 _45801).
Proof. exact (eq_refl (term106 _45801)). Qed.
Lemma lem3970184 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term112 _101508 s t _45802 _45800 _45801) = (term113 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970183 _45801) (@lem3970181 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970185 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term114 _101508 s t _45802 _45800 _45801) = (term112 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem17362 (term110 _45801) (term115 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970186 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term114 _101508 s t _45802 _45800 _45801) = (term113 _101508 s t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970185 _101508 s t _45802 _45800 _45801) (@lem3970184 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970188 (_45800 : int) : (term106 _45800) = (term106 _45800).
Proof. exact (eq_refl (term106 _45800)). Qed.
Lemma lem3970189 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term116 _101508 s t _45802 _45800 _45801) = (term117 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970188 _45800) (@lem3970186 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970190 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term118 _101508 s t _45802 _45800 _45801) = (term116 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem17362 (term110 _45800) (term119 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970218 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term118 _101508 s t _45802 _45800 _45801) = (term117 _101508 s t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970190 _101508 s t _45802 _45800 _45801) (@lem3970189 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970221 (x : int) (y : int) : (int_le x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3970222 (_45800 : int) : (term110 _45800) = (term121 _45800).
Proof. exact (@lem3970221 term122 _45800). Qed.
Lemma lem3970224 (n : nat) : (term123 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3970225 : term124 = term125.
Proof. exact (@lem3970224 (NUMERAL 0)). Qed.
Lemma lem3970226 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3970227 : term126 = term127.
Proof. exact (MK_COMB (@lem3970226) (@lem3970225)). Qed.
Lemma lem3970228 (_45800 : int) : (real_of_int _45800) = (real_of_int _45800).
Proof. exact (eq_refl (real_of_int _45800)). Qed.
Lemma lem3970229 (_45800 : int) : (term121 _45800) = (term128 _45800).
Proof. exact (MK_COMB (@lem3970227) (@lem3970228 _45800)). Qed.
Lemma lem3970231 (_45800 : int) : (term110 _45800) = (term128 _45800).
Proof. exact (TRANS (@lem3970222 _45800) (@lem3970229 _45800)). Qed.
Lemma lem3970234 (x : int) (y : int) : (int_le x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3970235 (_45801 : int) : (term110 _45801) = (term121 _45801).
Proof. exact (@lem3970234 term122 _45801). Qed.
Lemma lem3970237 (n : nat) : (term123 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3970238 : term124 = term125.
Proof. exact (@lem3970237 (NUMERAL 0)). Qed.
Lemma lem3970239 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3970240 : term126 = term127.
Proof. exact (MK_COMB (@lem3970239) (@lem3970238)). Qed.
Lemma lem3970241 (_45801 : int) : (real_of_int _45801) = (real_of_int _45801).
Proof. exact (eq_refl (real_of_int _45801)). Qed.
Lemma lem3970242 (_45801 : int) : (term121 _45801) = (term128 _45801).
Proof. exact (MK_COMB (@lem3970240) (@lem3970241 _45801)). Qed.
Lemma lem3970244 (_45801 : int) : (term110 _45801) = (term128 _45801).
Proof. exact (TRANS (@lem3970235 _45801) (@lem3970242 _45801)). Qed.
Lemma lem3970247 (x : int) (y : int) : (int_le x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3970248 (_45802 : int) : (term110 _45802) = (term121 _45802).
Proof. exact (@lem3970247 term122 _45802). Qed.
Lemma lem3970250 (n : nat) : (term123 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3970251 : term124 = term125.
Proof. exact (@lem3970250 (NUMERAL 0)). Qed.
Lemma lem3970252 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3970253 : term126 = term127.
Proof. exact (MK_COMB (@lem3970252) (@lem3970251)). Qed.
Lemma lem3970254 (_45802 : int) : (real_of_int _45802) = (real_of_int _45802).
Proof. exact (eq_refl (real_of_int _45802)). Qed.
Lemma lem3970255 (_45802 : int) : (term121 _45802) = (term128 _45802).
Proof. exact (MK_COMB (@lem3970253) (@lem3970254 _45802)). Qed.
Lemma lem3970257 (_45802 : int) : (term110 _45802) = (term128 _45802).
Proof. exact (TRANS (@lem3970248 _45802) (@lem3970255 _45802)). Qed.
Lemma lem3970265 (x : int) (y : int) : (int_lt x y) = (term129 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem3970266 (_45802 : int) (_45800 : int) (_45801 : int) : (term87 _45802 _45800 _45801) = (term130 _45802 _45800 _45801).
Proof. exact (@lem3970265 _45802 (int_add _45800 _45801)). Qed.
Lemma lem3970268 (x : int) (y : int) : (int_le x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3970269 (_45802 : int) (_45800 : int) (_45801 : int) : (term130 _45802 _45800 _45801) = (term131 _45802 _45800 _45801).
Proof. exact (@lem3970268 (term132 _45802) (int_add _45800 _45801)). Qed.
Lemma lem3970271 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3970272 (_45802 : int) : (term135 _45802) = (term136 _45802).
Proof. exact (@lem3970271 _45802 term137). Qed.
Lemma lem3970274 (n : nat) : (term123 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3970275 : term138 = term139.
Proof. exact (@lem3970274 term140). Qed.
Lemma lem3970276 (_45802 : int) : (term141 _45802) = (term141 _45802).
Proof. exact (eq_refl (term141 _45802)). Qed.
Lemma lem3970277 (_45802 : int) : (term136 _45802) = (term142 _45802).
Proof. exact (MK_COMB (@lem3970276 _45802) (@lem3970275)). Qed.
Lemma lem3970278 (_45802 : int) : (term135 _45802) = (term142 _45802).
Proof. exact (TRANS (@lem3970272 _45802) (@lem3970277 _45802)). Qed.
Lemma lem3970279 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3970280 (_45802 : int) : (term143 _45802) = (term144 _45802).
Proof. exact (MK_COMB (@lem3970279) (@lem3970278 _45802)). Qed.
Lemma lem3970282 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3970283 (_45800 : int) (_45801 : int) : (term133 _45800 _45801) = (term134 _45800 _45801).
Proof. exact (@lem3970282 _45800 _45801). Qed.
Lemma lem3970284 (_45802 : int) (_45800 : int) (_45801 : int) : (term131 _45802 _45800 _45801) = (term145 _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970280 _45802) (@lem3970283 _45800 _45801)). Qed.
Lemma lem3970285 (_45802 : int) (_45800 : int) (_45801 : int) : (term130 _45802 _45800 _45801) = (term145 _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970269 _45802 _45800 _45801) (@lem3970284 _45802 _45800 _45801)). Qed.
Lemma lem3970286 (_45802 : int) (_45800 : int) (_45801 : int) : (term87 _45802 _45800 _45801) = (term145 _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970266 _45802 _45800 _45801) (@lem3970285 _45802 _45800 _45801)). Qed.
Lemma lem3970288 {_101508 : Type'} (t : _101508 -> Prop) : (term29 _101508 t) = (term29 _101508 t).
Proof. exact (eq_refl (term29 _101508 t)). Qed.
Lemma lem3970289 {_101508 : Type'} (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term90 _101508 t _45802 _45800 _45801) = (term146 _101508 t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970288 _101508 t) (@lem3970286 _45802 _45800 _45801)). Qed.
Lemma lem3970291 {_101508 : Type'} (s : _101508 -> Prop) : (term29 _101508 s) = (term29 _101508 s).
Proof. exact (eq_refl (term29 _101508 s)). Qed.
Lemma lem3970292 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term95 _101508 s t _45802 _45800 _45801) = (term147 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970291 _101508 s) (@lem3970289 _101508 t _45802 _45800 _45801)). Qed.
Lemma lem3970295 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3970296 (_45802 : int) (_45800 : int) (_45801 : int) : (_45802 = (int_add _45800 _45801)) = ((real_of_int _45802) = (term133 _45800 _45801)).
Proof. exact (@lem3970295 _45802 (int_add _45800 _45801)). Qed.
Lemma lem3970300 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3970301 (_45800 : int) (_45801 : int) : (term133 _45800 _45801) = (term134 _45800 _45801).
Proof. exact (@lem3970300 _45800 _45801). Qed.
Lemma lem3970302 (_45802 : int) : (term148 _45802) = (term148 _45802).
Proof. exact (eq_refl (term148 _45802)). Qed.
Lemma lem3970303 (_45802 : int) (_45800 : int) (_45801 : int) : ((real_of_int _45802) = (term133 _45800 _45801)) = ((real_of_int _45802) = (term134 _45800 _45801)).
Proof. exact (MK_COMB (@lem3970302 _45802) (@lem3970301 _45800 _45801)). Qed.
Lemma lem3970305 (_45802 : int) (_45800 : int) (_45801 : int) : (_45802 = (int_add _45800 _45801)) = ((real_of_int _45802) = (term134 _45800 _45801)).
Proof. exact (TRANS (@lem3970296 _45802 _45800 _45801) (@lem3970303 _45802 _45800 _45801)). Qed.
Lemma lem3970306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970307 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term100 _101508 s t _45802 _45800 _45801) = (term149 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970306) (@lem3970292 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970308 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term102 _101508 s t _45802 _45800 _45801) = (term150 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970307 _101508 s t _45802 _45800 _45801) (@lem3970305 _45802 _45800 _45801)). Qed.
Lemma lem3970309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970310 (_45802 : int) : (term106 _45802) = (term151 _45802).
Proof. exact (MK_COMB (@lem3970309) (@lem3970257 _45802)). Qed.
Lemma lem3970311 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term108 _101508 s t _45802 _45800 _45801) = (term152 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970310 _45802) (@lem3970308 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970313 (_45801 : int) : (term106 _45801) = (term151 _45801).
Proof. exact (MK_COMB (@lem3970312) (@lem3970244 _45801)). Qed.
Lemma lem3970314 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term113 _101508 s t _45802 _45800 _45801) = (term153 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970313 _45801) (@lem3970311 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970316 (_45800 : int) : (term106 _45800) = (term151 _45800).
Proof. exact (MK_COMB (@lem3970315) (@lem3970231 _45800)). Qed.
Lemma lem3970317 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term117 _101508 s t _45802 _45800 _45801) = (term154 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970316 _45800) (@lem3970314 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970318 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term118 _101508 s t _45802 _45800 _45801) = (term154 _101508 s t _45802 _45800 _45801).
Proof. exact (TRANS (@lem3970218 _101508 s t _45802 _45800 _45801) (@lem3970317 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970322 (t : Prop) : (term155 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3970388 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term156 _101508 s t _45802 _45800 _45801) = (term154 _101508 s t _45802 _45800 _45801).
Proof. exact (@lem3970322 (term154 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3970389 (_45800 : int) : (term128 _45800) = (term157 _45800).
Proof. exact (@lem1988287 (real_of_int _45800) term125). Qed.
Lemma lem3970395 (_45800 : int) : (term158 _45800) = (term159 _45800).
Proof. exact (@lem1982792 (real_of_int _45800) term125). Qed.
Lemma lem3970397 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970398 : term125 = term161.
Proof. exact (@lem3970397 (NUMERAL 0)). Qed.
Lemma lem3970400 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3970401 : term164 = term165.
Proof. exact (@lem3970400 term140). Qed.
Lemma lem3970402 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970403 : term166 = term167.
Proof. exact (MK_COMB (@lem3970402) (@lem3970401)). Qed.
Lemma lem3970404 : term168 = term169.
Proof. exact (MK_COMB (@lem3970403) (@lem3970398)). Qed.
Lemma lem3970405 : term169 = term170.
Proof. exact (@lem1981613 term164 term125 term139 term139). Qed.
Lemma lem3970407 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970408 : term173 = term174.
Proof. exact (@lem3970407 term140 term140). Qed.
Lemma lem3970409 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970410 : term176 = term140.
Proof. exact (EQ_MP (@lem3970409) (@lem940073)). Qed.
Lemma lem3970411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970412 : term174 = term139.
Proof. exact (MK_COMB (@lem3970411) (@lem3970410)). Qed.
Lemma lem3970413 : term173 = term139.
Proof. exact (TRANS (@lem3970408) (@lem3970412)). Qed.
Lemma lem3970415 (x : nat) : (term177 x) = term125.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3970416 : term168 = term125.
Proof. exact (@lem3970415 term140). Qed.
Lemma lem3970417 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3970418 : term178 = term179.
Proof. exact (MK_COMB (@lem3970417) (@lem3970416)). Qed.
Lemma lem3970419 : term170 = term161.
Proof. exact (MK_COMB (@lem3970418) (@lem3970413)). Qed.
Lemma lem3970420 : term169 = term161.
Proof. exact (TRANS (@lem3970405) (@lem3970419)). Qed.
Lemma lem3970421 : term168 = term161.
Proof. exact (TRANS (@lem3970404) (@lem3970420)). Qed.
Lemma lem3970423 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3970424 : term161 = term125.
Proof. exact (@lem3970423 term125). Qed.
Lemma lem3970425 : term168 = term125.
Proof. exact (TRANS (@lem3970421) (@lem3970424)). Qed.
Lemma lem3970426 (_45800 : int) : (term141 _45800) = (term141 _45800).
Proof. exact (eq_refl (term141 _45800)). Qed.
Lemma lem3970427 (_45800 : int) : (term159 _45800) = (term181 _45800).
Proof. exact (MK_COMB (@lem3970426 _45800) (@lem3970425)). Qed.
Lemma lem3970428 (_45800 : int) : (term181 _45800) = (real_of_int _45800).
Proof. exact (@lem1982723 (real_of_int _45800)). Qed.
Lemma lem3970429 (_45800 : int) : (term159 _45800) = (real_of_int _45800).
Proof. exact (TRANS (@lem3970427 _45800) (@lem3970428 _45800)). Qed.
Lemma lem3970431 (_45800 : int) : (term158 _45800) = (real_of_int _45800).
Proof. exact (TRANS (@lem3970395 _45800) (@lem3970429 _45800)). Qed.
Lemma lem3970432 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3970433 (_45800 : int) : (term182 _45800) = (term183 _45800).
Proof. exact (MK_COMB (@lem3970432) (@lem3970431 _45800)). Qed.
Lemma lem3970434 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970435 (_45800 : int) : (term157 _45800) = (term184 _45800).
Proof. exact (MK_COMB (@lem3970433 _45800) (@lem3970434)). Qed.
Lemma lem3970436 (_45800 : int) : (term128 _45800) = (term184 _45800).
Proof. exact (TRANS (@lem3970389 _45800) (@lem3970435 _45800)). Qed.
Lemma lem3970437 (_45801 : int) : (term128 _45801) = (term157 _45801).
Proof. exact (@lem1988287 (real_of_int _45801) term125). Qed.
Lemma lem3970443 (_45801 : int) : (term158 _45801) = (term159 _45801).
Proof. exact (@lem1982792 (real_of_int _45801) term125). Qed.
Lemma lem3970445 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970446 : term125 = term161.
Proof. exact (@lem3970445 (NUMERAL 0)). Qed.
Lemma lem3970448 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3970449 : term164 = term165.
Proof. exact (@lem3970448 term140). Qed.
Lemma lem3970450 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970451 : term166 = term167.
Proof. exact (MK_COMB (@lem3970450) (@lem3970449)). Qed.
Lemma lem3970452 : term168 = term169.
Proof. exact (MK_COMB (@lem3970451) (@lem3970446)). Qed.
Lemma lem3970453 : term169 = term170.
Proof. exact (@lem1981613 term164 term125 term139 term139). Qed.
Lemma lem3970455 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970456 : term173 = term174.
Proof. exact (@lem3970455 term140 term140). Qed.
Lemma lem3970457 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970458 : term176 = term140.
Proof. exact (EQ_MP (@lem3970457) (@lem940073)). Qed.
Lemma lem3970459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970460 : term174 = term139.
Proof. exact (MK_COMB (@lem3970459) (@lem3970458)). Qed.
Lemma lem3970461 : term173 = term139.
Proof. exact (TRANS (@lem3970456) (@lem3970460)). Qed.
Lemma lem3970463 (x : nat) : (term177 x) = term125.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3970464 : term168 = term125.
Proof. exact (@lem3970463 term140). Qed.
Lemma lem3970465 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3970466 : term178 = term179.
Proof. exact (MK_COMB (@lem3970465) (@lem3970464)). Qed.
Lemma lem3970467 : term170 = term161.
Proof. exact (MK_COMB (@lem3970466) (@lem3970461)). Qed.
Lemma lem3970468 : term169 = term161.
Proof. exact (TRANS (@lem3970453) (@lem3970467)). Qed.
Lemma lem3970469 : term168 = term161.
Proof. exact (TRANS (@lem3970452) (@lem3970468)). Qed.
Lemma lem3970471 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3970472 : term161 = term125.
Proof. exact (@lem3970471 term125). Qed.
Lemma lem3970473 : term168 = term125.
Proof. exact (TRANS (@lem3970469) (@lem3970472)). Qed.
Lemma lem3970474 (_45801 : int) : (term141 _45801) = (term141 _45801).
Proof. exact (eq_refl (term141 _45801)). Qed.
Lemma lem3970475 (_45801 : int) : (term159 _45801) = (term181 _45801).
Proof. exact (MK_COMB (@lem3970474 _45801) (@lem3970473)). Qed.
Lemma lem3970476 (_45801 : int) : (term181 _45801) = (real_of_int _45801).
Proof. exact (@lem1982723 (real_of_int _45801)). Qed.
Lemma lem3970477 (_45801 : int) : (term159 _45801) = (real_of_int _45801).
Proof. exact (TRANS (@lem3970475 _45801) (@lem3970476 _45801)). Qed.
Lemma lem3970479 (_45801 : int) : (term158 _45801) = (real_of_int _45801).
Proof. exact (TRANS (@lem3970443 _45801) (@lem3970477 _45801)). Qed.
Lemma lem3970480 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3970481 (_45801 : int) : (term182 _45801) = (term183 _45801).
Proof. exact (MK_COMB (@lem3970480) (@lem3970479 _45801)). Qed.
Lemma lem3970482 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970483 (_45801 : int) : (term157 _45801) = (term184 _45801).
Proof. exact (MK_COMB (@lem3970481 _45801) (@lem3970482)). Qed.
Lemma lem3970484 (_45801 : int) : (term128 _45801) = (term184 _45801).
Proof. exact (TRANS (@lem3970437 _45801) (@lem3970483 _45801)). Qed.
Lemma lem3970485 (_45802 : int) : (term128 _45802) = (term157 _45802).
Proof. exact (@lem1988287 (real_of_int _45802) term125). Qed.
Lemma lem3970491 (_45802 : int) : (term158 _45802) = (term159 _45802).
Proof. exact (@lem1982792 (real_of_int _45802) term125). Qed.
Lemma lem3970493 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970494 : term125 = term161.
Proof. exact (@lem3970493 (NUMERAL 0)). Qed.
Lemma lem3970496 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3970497 : term164 = term165.
Proof. exact (@lem3970496 term140). Qed.
Lemma lem3970498 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970499 : term166 = term167.
Proof. exact (MK_COMB (@lem3970498) (@lem3970497)). Qed.
Lemma lem3970500 : term168 = term169.
Proof. exact (MK_COMB (@lem3970499) (@lem3970494)). Qed.
Lemma lem3970501 : term169 = term170.
Proof. exact (@lem1981613 term164 term125 term139 term139). Qed.
Lemma lem3970503 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970504 : term173 = term174.
Proof. exact (@lem3970503 term140 term140). Qed.
Lemma lem3970505 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970506 : term176 = term140.
Proof. exact (EQ_MP (@lem3970505) (@lem940073)). Qed.
Lemma lem3970507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970508 : term174 = term139.
Proof. exact (MK_COMB (@lem3970507) (@lem3970506)). Qed.
Lemma lem3970509 : term173 = term139.
Proof. exact (TRANS (@lem3970504) (@lem3970508)). Qed.
Lemma lem3970511 (x : nat) : (term177 x) = term125.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3970512 : term168 = term125.
Proof. exact (@lem3970511 term140). Qed.
Lemma lem3970513 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3970514 : term178 = term179.
Proof. exact (MK_COMB (@lem3970513) (@lem3970512)). Qed.
Lemma lem3970515 : term170 = term161.
Proof. exact (MK_COMB (@lem3970514) (@lem3970509)). Qed.
Lemma lem3970516 : term169 = term161.
Proof. exact (TRANS (@lem3970501) (@lem3970515)). Qed.
Lemma lem3970517 : term168 = term161.
Proof. exact (TRANS (@lem3970500) (@lem3970516)). Qed.
Lemma lem3970519 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3970520 : term161 = term125.
Proof. exact (@lem3970519 term125). Qed.
Lemma lem3970521 : term168 = term125.
Proof. exact (TRANS (@lem3970517) (@lem3970520)). Qed.
Lemma lem3970522 (_45802 : int) : (term141 _45802) = (term141 _45802).
Proof. exact (eq_refl (term141 _45802)). Qed.
Lemma lem3970523 (_45802 : int) : (term159 _45802) = (term181 _45802).
Proof. exact (MK_COMB (@lem3970522 _45802) (@lem3970521)). Qed.
Lemma lem3970524 (_45802 : int) : (term181 _45802) = (real_of_int _45802).
Proof. exact (@lem1982723 (real_of_int _45802)). Qed.
Lemma lem3970525 (_45802 : int) : (term159 _45802) = (real_of_int _45802).
Proof. exact (TRANS (@lem3970523 _45802) (@lem3970524 _45802)). Qed.
Lemma lem3970527 (_45802 : int) : (term158 _45802) = (real_of_int _45802).
Proof. exact (TRANS (@lem3970491 _45802) (@lem3970525 _45802)). Qed.
Lemma lem3970528 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3970529 (_45802 : int) : (term182 _45802) = (term183 _45802).
Proof. exact (MK_COMB (@lem3970528) (@lem3970527 _45802)). Qed.
Lemma lem3970530 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970531 (_45802 : int) : (term157 _45802) = (term184 _45802).
Proof. exact (MK_COMB (@lem3970529 _45802) (@lem3970530)). Qed.
Lemma lem3970532 (_45802 : int) : (term128 _45802) = (term184 _45802).
Proof. exact (TRANS (@lem3970485 _45802) (@lem3970531 _45802)). Qed.
Lemma lem3970535 (_45800 : int) (_45801 : int) (_45802 : int) : (term145 _45802 _45800 _45801) = (term185 _45800 _45801 _45802).
Proof. exact (@lem1988287 (term134 _45800 _45801) (term142 _45802)). Qed.
Lemma lem3970553 (_45800 : int) (_45801 : int) (_45802 : int) : (term186 _45800 _45801 _45802) = (term187 _45800 _45801 _45802).
Proof. exact (@lem1982792 (term134 _45800 _45801) (term142 _45802)). Qed.
Lemma lem3970554 (_45802 : int) : (term188 _45802) = (term189 _45802).
Proof. exact (@lem1982781 (real_of_int _45802) term164 term139). Qed.
Lemma lem3970556 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970557 : term139 = term190.
Proof. exact (@lem3970556 term140). Qed.
Lemma lem3970559 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3970560 : term164 = term165.
Proof. exact (@lem3970559 term140). Qed.
Lemma lem3970561 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970562 : term166 = term167.
Proof. exact (MK_COMB (@lem3970561) (@lem3970560)). Qed.
Lemma lem3970563 : term191 = term192.
Proof. exact (MK_COMB (@lem3970562) (@lem3970557)). Qed.
Lemma lem3970564 : term192 = term193.
Proof. exact (@lem1981613 term164 term139 term139 term139). Qed.
Lemma lem3970566 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970567 : term173 = term174.
Proof. exact (@lem3970566 term140 term140). Qed.
Lemma lem3970568 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970569 : term176 = term140.
Proof. exact (EQ_MP (@lem3970568) (@lem940073)). Qed.
Lemma lem3970570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970571 : term174 = term139.
Proof. exact (MK_COMB (@lem3970570) (@lem3970569)). Qed.
Lemma lem3970572 : term173 = term139.
Proof. exact (TRANS (@lem3970567) (@lem3970571)). Qed.
Lemma lem3970574 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3970575 : term191 = term196.
Proof. exact (@lem3970574 term140 term140). Qed.
Lemma lem3970576 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970577 : term176 = term140.
Proof. exact (EQ_MP (@lem3970576) (@lem940073)). Qed.
Lemma lem3970578 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970579 : term174 = term139.
Proof. exact (MK_COMB (@lem3970578) (@lem3970577)). Qed.
Lemma lem3970580 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3970581 : term196 = term164.
Proof. exact (MK_COMB (@lem3970580) (@lem3970579)). Qed.
Lemma lem3970582 : term191 = term164.
Proof. exact (TRANS (@lem3970575) (@lem3970581)). Qed.
Lemma lem3970583 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3970584 : term197 = term198.
Proof. exact (MK_COMB (@lem3970583) (@lem3970582)). Qed.
Lemma lem3970585 : term193 = term165.
Proof. exact (MK_COMB (@lem3970584) (@lem3970572)). Qed.
Lemma lem3970586 : term192 = term165.
Proof. exact (TRANS (@lem3970564) (@lem3970585)). Qed.
Lemma lem3970587 : term191 = term165.
Proof. exact (TRANS (@lem3970563) (@lem3970586)). Qed.
Lemma lem3970589 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3970590 : term165 = term164.
Proof. exact (@lem3970589 term164). Qed.
Lemma lem3970591 : term191 = term164.
Proof. exact (TRANS (@lem3970587) (@lem3970590)). Qed.
Lemma lem3970594 (_45802 : int) : (term199 _45802) = (term199 _45802).
Proof. exact (eq_refl (term199 _45802)). Qed.
Lemma lem3970595 (_45802 : int) : (term189 _45802) = (term200 _45802).
Proof. exact (MK_COMB (@lem3970594 _45802) (@lem3970591)). Qed.
Lemma lem3970596 (_45802 : int) : (term188 _45802) = (term200 _45802).
Proof. exact (TRANS (@lem3970554 _45802) (@lem3970595 _45802)). Qed.
Lemma lem3970597 (_45800 : int) (_45801 : int) : (term201 _45800 _45801) = (term201 _45800 _45801).
Proof. exact (eq_refl (term201 _45800 _45801)). Qed.
Lemma lem3970598 (_45800 : int) (_45801 : int) (_45802 : int) : (term187 _45800 _45801 _45802) = (term202 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970597 _45800 _45801) (@lem3970596 _45802)). Qed.
Lemma lem3970603 (_45800 : int) (_45801 : int) (_45802 : int) : (term202 _45800 _45801 _45802) = (term203 _45800 _45801 _45802).
Proof. exact (@lem1982755 (real_of_int _45800) (real_of_int _45801) (term200 _45802)). Qed.
Lemma lem3970604 (_45800 : int) (_45801 : int) (_45802 : int) : (term187 _45800 _45801 _45802) = (term203 _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970598 _45800 _45801 _45802) (@lem3970603 _45800 _45801 _45802)). Qed.
Lemma lem3970606 (_45800 : int) (_45801 : int) (_45802 : int) : (term186 _45800 _45801 _45802) = (term203 _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970553 _45800 _45801 _45802) (@lem3970604 _45800 _45801 _45802)). Qed.
Lemma lem3970607 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3970608 (_45800 : int) (_45801 : int) (_45802 : int) : (term204 _45800 _45801 _45802) = (term205 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970607) (@lem3970606 _45800 _45801 _45802)). Qed.
Lemma lem3970609 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970610 (_45800 : int) (_45801 : int) (_45802 : int) : (term185 _45800 _45801 _45802) = (term206 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970608 _45800 _45801 _45802) (@lem3970609)). Qed.
Lemma lem3970611 (_45800 : int) (_45801 : int) (_45802 : int) : (term145 _45802 _45800 _45801) = (term206 _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970535 _45800 _45801 _45802) (@lem3970610 _45800 _45801 _45802)). Qed.
Lemma lem3970613 {_101508 : Type'} (t : _101508 -> Prop) : (term29 _101508 t) = (term29 _101508 t).
Proof. exact (eq_refl (term29 _101508 t)). Qed.
Lemma lem3970614 {_101508 : Type'} (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term146 _101508 t _45802 _45800 _45801) = (term207 _101508 t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970613 _101508 t) (@lem3970611 _45800 _45801 _45802)). Qed.
Lemma lem3970616 {_101508 : Type'} (s : _101508 -> Prop) : (term29 _101508 s) = (term29 _101508 s).
Proof. exact (eq_refl (term29 _101508 s)). Qed.
Lemma lem3970617 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term147 _101508 s t _45802 _45800 _45801) = (term208 _101508 s t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970616 _101508 s) (@lem3970614 _101508 t _45800 _45801 _45802)). Qed.
Lemma lem3970618 (_45802 : int) (_45800 : int) (_45801 : int) : ((real_of_int _45802) = (term134 _45800 _45801)) = ((term209 _45802 _45800 _45801) = term125).
Proof. exact (@lem1988293 (real_of_int _45802) (term134 _45800 _45801)). Qed.
Lemma lem3970630 (_45802 : int) (_45800 : int) (_45801 : int) : (term209 _45802 _45800 _45801) = (term210 _45802 _45800 _45801).
Proof. exact (@lem1982792 (real_of_int _45802) (term134 _45800 _45801)). Qed.
Lemma lem3970637 (_45800 : int) (_45801 : int) : (term211 _45800 _45801) = (term212 _45800 _45801).
Proof. exact (@lem1982781 (real_of_int _45800) term164 (real_of_int _45801)). Qed.
Lemma lem3970638 (_45802 : int) : (term141 _45802) = (term141 _45802).
Proof. exact (eq_refl (term141 _45802)). Qed.
Lemma lem3970639 (_45802 : int) (_45800 : int) (_45801 : int) : (term210 _45802 _45800 _45801) = (term213 _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3970638 _45802) (@lem3970637 _45800 _45801)). Qed.
Lemma lem3970640 (_45800 : int) (_45802 : int) (_45801 : int) : (term213 _45802 _45800 _45801) = (term214 _45800 _45802 _45801).
Proof. exact (@lem1982757 (term215 _45800) (real_of_int _45802) (term215 _45801)). Qed.
Lemma lem3970641 (_45801 : int) (_45802 : int) : (term216 _45802 _45801) = (term217 _45801 _45802).
Proof. exact (@lem1982761 (term215 _45801) (real_of_int _45802)). Qed.
Lemma lem3970642 (_45800 : int) : (term199 _45800) = (term199 _45800).
Proof. exact (eq_refl (term199 _45800)). Qed.
Lemma lem3970643 (_45800 : int) (_45801 : int) (_45802 : int) : (term214 _45800 _45802 _45801) = (term218 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970642 _45800) (@lem3970641 _45801 _45802)). Qed.
Lemma lem3970644 (_45800 : int) (_45801 : int) (_45802 : int) : (term213 _45802 _45800 _45801) = (term218 _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970640 _45800 _45802 _45801) (@lem3970643 _45800 _45801 _45802)). Qed.
Lemma lem3970645 (_45800 : int) (_45801 : int) (_45802 : int) : (term210 _45802 _45800 _45801) = (term218 _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970639 _45802 _45800 _45801) (@lem3970644 _45800 _45801 _45802)). Qed.
Lemma lem3970647 (_45800 : int) (_45801 : int) (_45802 : int) : (term209 _45802 _45800 _45801) = (term218 _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970630 _45802 _45800 _45801) (@lem3970645 _45800 _45801 _45802)). Qed.
Lemma lem3970648 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3970649 (_45800 : int) (_45801 : int) (_45802 : int) : (term219 _45802 _45800 _45801) = (term220 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970648) (@lem3970647 _45800 _45801 _45802)). Qed.
Lemma lem3970650 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970651 (_45800 : int) (_45801 : int) (_45802 : int) : ((term209 _45802 _45800 _45801) = term125) = ((term218 _45800 _45801 _45802) = term125).
Proof. exact (MK_COMB (@lem3970649 _45800 _45801 _45802) (@lem3970650)). Qed.
Lemma lem3970652 (_45800 : int) (_45801 : int) (_45802 : int) : ((real_of_int _45802) = (term134 _45800 _45801)) = ((term218 _45800 _45801 _45802) = term125).
Proof. exact (TRANS (@lem3970618 _45802 _45800 _45801) (@lem3970651 _45800 _45801 _45802)). Qed.
Lemma lem3970653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970654 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term149 _101508 s t _45802 _45800 _45801) = (term221 _101508 s t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970653) (@lem3970617 _101508 s t _45800 _45801 _45802)). Qed.
Lemma lem3970655 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term150 _101508 s t _45802 _45800 _45801) = (term222 _101508 s t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970654 _101508 s t _45800 _45801 _45802) (@lem3970652 _45800 _45801 _45802)). Qed.
Lemma lem3970656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970657 (_45802 : int) : (term151 _45802) = (term223 _45802).
Proof. exact (MK_COMB (@lem3970656) (@lem3970532 _45802)). Qed.
Lemma lem3970658 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term152 _101508 s t _45802 _45800 _45801) = (term224 _101508 s t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970657 _45802) (@lem3970655 _101508 s t _45800 _45801 _45802)). Qed.
Lemma lem3970659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970660 (_45801 : int) : (term151 _45801) = (term223 _45801).
Proof. exact (MK_COMB (@lem3970659) (@lem3970484 _45801)). Qed.
Lemma lem3970661 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term153 _101508 s t _45802 _45800 _45801) = (term225 _101508 s t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970660 _45801) (@lem3970658 _101508 s t _45800 _45801 _45802)). Qed.
Lemma lem3970662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3970663 (_45800 : int) : (term151 _45800) = (term223 _45800).
Proof. exact (MK_COMB (@lem3970662) (@lem3970436 _45800)). Qed.
Lemma lem3970664 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term154 _101508 s t _45802 _45800 _45801) = (term226 _101508 s t _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970663 _45800) (@lem3970661 _101508 s t _45800 _45801 _45802)). Qed.
Lemma lem3970709 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) : (term156 _101508 s t _45802 _45800 _45801) = (term226 _101508 s t _45800 _45801 _45802).
Proof. exact (TRANS (@lem3970388 _101508 s t _45802 _45800 _45801) (@lem3970664 _101508 s t _45800 _45801 _45802)). Qed.
Lemma lem3970713 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term226 _101508 s t _45800 _45801 _45802.
Proof. exact (h1). Qed.
Lemma lem3970714 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term225 _101508 s t _45800 _45801 _45802.
Proof. exact (proj2 (@lem3970713 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970716 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term224 _101508 s t _45800 _45801 _45802.
Proof. exact (proj2 (@lem3970714 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970718 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term222 _101508 s t _45800 _45801 _45802.
Proof. exact (proj2 (@lem3970716 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970720 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : (term218 _45800 _45801 _45802) = term125.
Proof. exact (proj2 (@lem3970718 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970721 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term208 _101508 s t _45800 _45801 _45802.
Proof. exact (proj1 (@lem3970718 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970722 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term207 _101508 t _45800 _45801 _45802.
Proof. exact (proj2 (@lem3970721 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970724 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term206 _45800 _45801 _45802.
Proof. exact (proj2 (@lem3970722 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970727 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3970728 : term227 = term228.
Proof. exact (@lem3970727 term125 term139). Qed.
Lemma lem3970730 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970731 : term139 = term190.
Proof. exact (@lem3970730 term140). Qed.
Lemma lem3970733 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970734 : term125 = term161.
Proof. exact (@lem3970733 (NUMERAL 0)). Qed.
Lemma lem3970735 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3970736 : term229 = term230.
Proof. exact (MK_COMB (@lem3970735) (@lem3970734)). Qed.
Lemma lem3970737 : term228 = term231.
Proof. exact (MK_COMB (@lem3970736) (@lem3970731)). Qed.
Lemma lem3970738 : term232.
Proof. exact (@lem1980255 term125 term139 term139 term139). Qed.
Lemma lem3970740 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970741 : term228 = term234.
Proof. exact (@lem3970740 (NUMERAL 0) term140). Qed.
Lemma lem3970742 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970743 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970744 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970743 h1) (fun h1 : term234 = True => @lem3970742)). Qed.
Lemma lem3970745 : term234 = True.
Proof. exact (EQ_MP (@lem3970744) (@lem3970742)). Qed.
Lemma lem3970746 : term228 = True.
Proof. exact (TRANS (@lem3970741) (@lem3970745)). Qed.
Lemma lem3970747 : True = term228.
Proof. exact (SYM (@lem3970746)). Qed.
Lemma lem3970748 : term228.
Proof. exact (EQ_MP (@lem3970747) (@lem0)). Qed.
Lemma lem3970749 : term236.
Proof. exact (@lem3970738 (@lem3970748)). Qed.
Lemma lem3970751 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970752 : term228 = term234.
Proof. exact (@lem3970751 (NUMERAL 0) term140). Qed.
Lemma lem3970753 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970754 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970755 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970754 h1) (fun h1 : term234 = True => @lem3970753)). Qed.
Lemma lem3970756 : term234 = True.
Proof. exact (EQ_MP (@lem3970755) (@lem3970753)). Qed.
Lemma lem3970757 : term228 = True.
Proof. exact (TRANS (@lem3970752) (@lem3970756)). Qed.
Lemma lem3970758 : True = term228.
Proof. exact (SYM (@lem3970757)). Qed.
Lemma lem3970759 : term228.
Proof. exact (EQ_MP (@lem3970758) (@lem0)). Qed.
Lemma lem3970760 : term231 = term237.
Proof. exact (@lem3970749 (@lem3970759)). Qed.
Lemma lem3970762 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970763 : term173 = term174.
Proof. exact (@lem3970762 term140 term140). Qed.
Lemma lem3970764 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970765 : term176 = term140.
Proof. exact (EQ_MP (@lem3970764) (@lem940073)). Qed.
Lemma lem3970766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970767 : term174 = term139.
Proof. exact (MK_COMB (@lem3970766) (@lem3970765)). Qed.
Lemma lem3970768 : term173 = term139.
Proof. exact (TRANS (@lem3970763) (@lem3970767)). Qed.
Lemma lem3970770 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3970771 : term239 = term125.
Proof. exact (@lem3970770 term140). Qed.
Lemma lem3970772 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3970773 : term240 = term229.
Proof. exact (MK_COMB (@lem3970772) (@lem3970771)). Qed.
Lemma lem3970774 : term237 = term228.
Proof. exact (MK_COMB (@lem3970773) (@lem3970768)). Qed.
Lemma lem3970776 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970777 : term228 = term234.
Proof. exact (@lem3970776 (NUMERAL 0) term140). Qed.
Lemma lem3970778 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970779 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970780 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970779 h1) (fun h1 : term234 = True => @lem3970778)). Qed.
Lemma lem3970781 : term234 = True.
Proof. exact (EQ_MP (@lem3970780) (@lem3970778)). Qed.
Lemma lem3970782 : term228 = True.
Proof. exact (TRANS (@lem3970777) (@lem3970781)). Qed.
Lemma lem3970783 : term237 = True.
Proof. exact (TRANS (@lem3970774) (@lem3970782)). Qed.
Lemma lem3970784 : term231 = True.
Proof. exact (TRANS (@lem3970760) (@lem3970783)). Qed.
Lemma lem3970785 : term228 = True.
Proof. exact (TRANS (@lem3970737) (@lem3970784)). Qed.
Lemma lem3970786 : term227 = True.
Proof. exact (TRANS (@lem3970728) (@lem3970785)). Qed.
Lemma lem3970787 : True = term227.
Proof. exact (SYM (@lem3970786)). Qed.
Lemma lem3970788 : term227.
Proof. exact (EQ_MP (@lem3970787) (@lem0)). Qed.
Lemma lem3970789 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term241 _45800 _45801 _45802.
Proof. exact (conj (@lem3970788) (@lem3970724 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970791 (x : real) (y : real) : term242 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3970792 (_45800 : int) (_45801 : int) (_45802 : int) : term243 _45800 _45801 _45802.
Proof. exact (@lem3970791 term139 (term203 _45800 _45801 _45802)). Qed.
Lemma lem3970793 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term244 _45800 _45801 _45802.
Proof. exact (@lem3970792 _45800 _45801 _45802 (@lem3970789 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970794 (_45800 : int) (_45801 : int) (_45802 : int) : (term245 _45800 _45801 _45802) = (term203 _45800 _45801 _45802).
Proof. exact (@lem1982733 (term203 _45800 _45801 _45802)). Qed.
Lemma lem3970795 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3970796 (_45800 : int) (_45801 : int) (_45802 : int) : (term246 _45800 _45801 _45802) = (term205 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970795) (@lem3970794 _45800 _45801 _45802)). Qed.
Lemma lem3970797 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970798 (_45800 : int) (_45801 : int) (_45802 : int) : (term244 _45800 _45801 _45802) = (term206 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970796 _45800 _45801 _45802) (@lem3970797)). Qed.
Lemma lem3970799 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term206 _45800 _45801 _45802.
Proof. exact (EQ_MP (@lem3970798 _45800 _45801 _45802) (@lem3970793 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970801 (y : real) : term247 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3970802 (_45800 : int) (_45801 : int) (_45802 : int) : term248 _45800 _45801 _45802.
Proof. exact (@lem3970801 (term218 _45800 _45801 _45802)). Qed.
Lemma lem3970803 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term249 _45800 _45801 _45802.
Proof. exact (@lem3970802 _45800 _45801 _45802 (@lem3970720 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970804 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term250 _45800 _45801 _45802.
Proof. exact (@lem3970803 _101508 s t _45800 _45801 _45802 h1 term139). Qed.
Lemma lem3970805 (_45800 : int) (_45801 : int) (_45802 : int) : (term250 _45800 _45801 _45802) = ((term251 _45800 _45801 _45802) = term125).
Proof. exact (eq_refl (term250 _45800 _45801 _45802)). Qed.
Lemma lem3970806 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : (term251 _45800 _45801 _45802) = term125.
Proof. exact (EQ_MP (@lem3970805 _45800 _45801 _45802) (@lem3970804 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970807 (_45800 : int) (_45801 : int) (_45802 : int) : (term251 _45800 _45801 _45802) = (term218 _45800 _45801 _45802).
Proof. exact (@lem1982733 (term218 _45800 _45801 _45802)). Qed.
Lemma lem3970808 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3970809 (_45800 : int) (_45801 : int) (_45802 : int) : (term252 _45800 _45801 _45802) = (term220 _45800 _45801 _45802).
Proof. exact (MK_COMB (@lem3970808) (@lem3970807 _45800 _45801 _45802)). Qed.
Lemma lem3970810 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3970811 (_45800 : int) (_45801 : int) (_45802 : int) : ((term251 _45800 _45801 _45802) = term125) = ((term218 _45800 _45801 _45802) = term125).
Proof. exact (MK_COMB (@lem3970809 _45800 _45801 _45802) (@lem3970810)). Qed.
Lemma lem3970812 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : (term218 _45800 _45801 _45802) = term125.
Proof. exact (EQ_MP (@lem3970811 _45800 _45801 _45802) (@lem3970806 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970813 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term253 _45800 _45801 _45802.
Proof. exact (conj (@lem3970812 _101508 s t _45800 _45801 _45802 h1) (@lem3970799 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970815 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3970816 (_45800 : int) (_45801 : int) (_45802 : int) : term255 _45800 _45801 _45802.
Proof. exact (@lem3970815 (term218 _45800 _45801 _45802) (term203 _45800 _45801 _45802)). Qed.
Lemma lem3970817 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term256 _45800 _45801 _45802.
Proof. exact (@lem3970816 _45800 _45801 _45802 (@lem3970813 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3970818 (_45800 : int) (_45801 : int) (_45802 : int) : (term257 _45800 _45801 _45802) = (term258 _45800 _45801 _45802).
Proof. exact (@lem1982753 (term215 _45800) (real_of_int _45800) (term217 _45801 _45802) (term259 _45801 _45802)). Qed.
Lemma lem3970819 (_45800 : int) : (term260 _45800) = (term261 _45800).
Proof. exact (@lem1982713 term164 (real_of_int _45800)). Qed.
Lemma lem3970821 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970822 : term139 = term190.
Proof. exact (@lem3970821 term140). Qed.
Lemma lem3970824 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3970825 : term164 = term165.
Proof. exact (@lem3970824 term140). Qed.
Lemma lem3970826 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3970827 : term262 = term263.
Proof. exact (MK_COMB (@lem3970826) (@lem3970825)). Qed.
Lemma lem3970828 : term264 = term265.
Proof. exact (MK_COMB (@lem3970827) (@lem3970822)). Qed.
Lemma lem3970829 : term266.
Proof. exact (@lem1981473 term164 term139 term139 term139 term125 term139). Qed.
Lemma lem3970831 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970832 : term228 = term234.
Proof. exact (@lem3970831 (NUMERAL 0) term140). Qed.
Lemma lem3970833 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970834 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970835 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970834 h1) (fun h1 : term234 = True => @lem3970833)). Qed.
Lemma lem3970836 : term234 = True.
Proof. exact (EQ_MP (@lem3970835) (@lem3970833)). Qed.
Lemma lem3970837 : term228 = True.
Proof. exact (TRANS (@lem3970832) (@lem3970836)). Qed.
Lemma lem3970838 : True = term228.
Proof. exact (SYM (@lem3970837)). Qed.
Lemma lem3970839 : term228.
Proof. exact (EQ_MP (@lem3970838) (@lem0)). Qed.
Lemma lem3970840 : term267.
Proof. exact (@lem3970829 (@lem3970839)). Qed.
Lemma lem3970842 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970843 : term228 = term234.
Proof. exact (@lem3970842 (NUMERAL 0) term140). Qed.
Lemma lem3970844 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970845 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970846 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970845 h1) (fun h1 : term234 = True => @lem3970844)). Qed.
Lemma lem3970847 : term234 = True.
Proof. exact (EQ_MP (@lem3970846) (@lem3970844)). Qed.
Lemma lem3970848 : term228 = True.
Proof. exact (TRANS (@lem3970843) (@lem3970847)). Qed.
Lemma lem3970849 : True = term228.
Proof. exact (SYM (@lem3970848)). Qed.
Lemma lem3970850 : term228.
Proof. exact (EQ_MP (@lem3970849) (@lem0)). Qed.
Lemma lem3970851 : term268.
Proof. exact (@lem3970840 (@lem3970850)). Qed.
Lemma lem3970853 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970854 : term228 = term234.
Proof. exact (@lem3970853 (NUMERAL 0) term140). Qed.
Lemma lem3970855 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970856 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970857 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970856 h1) (fun h1 : term234 = True => @lem3970855)). Qed.
Lemma lem3970858 : term234 = True.
Proof. exact (EQ_MP (@lem3970857) (@lem3970855)). Qed.
Lemma lem3970859 : term228 = True.
Proof. exact (TRANS (@lem3970854) (@lem3970858)). Qed.
Lemma lem3970860 : True = term228.
Proof. exact (SYM (@lem3970859)). Qed.
Lemma lem3970861 : term228.
Proof. exact (EQ_MP (@lem3970860) (@lem0)). Qed.
Lemma lem3970862 : term269.
Proof. exact (@lem3970851 (@lem3970861)). Qed.
Lemma lem3970864 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970865 : term173 = term174.
Proof. exact (@lem3970864 term140 term140). Qed.
Lemma lem3970866 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970867 : term176 = term140.
Proof. exact (EQ_MP (@lem3970866) (@lem940073)). Qed.
Lemma lem3970868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970869 : term174 = term139.
Proof. exact (MK_COMB (@lem3970868) (@lem3970867)). Qed.
Lemma lem3970870 : term173 = term139.
Proof. exact (TRANS (@lem3970865) (@lem3970869)). Qed.
Lemma lem3970872 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3970873 : term191 = term196.
Proof. exact (@lem3970872 term140 term140). Qed.
Lemma lem3970874 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970875 : term176 = term140.
Proof. exact (EQ_MP (@lem3970874) (@lem940073)). Qed.
Lemma lem3970876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970877 : term174 = term139.
Proof. exact (MK_COMB (@lem3970876) (@lem3970875)). Qed.
Lemma lem3970878 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3970879 : term196 = term164.
Proof. exact (MK_COMB (@lem3970878) (@lem3970877)). Qed.
Lemma lem3970880 : term191 = term164.
Proof. exact (TRANS (@lem3970873) (@lem3970879)). Qed.
Lemma lem3970881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3970882 : term270 = term262.
Proof. exact (MK_COMB (@lem3970881) (@lem3970880)). Qed.
Lemma lem3970883 : term271 = term264.
Proof. exact (MK_COMB (@lem3970882) (@lem3970870)). Qed.
Lemma lem3970885 (m : nat) : (term272 m) = term125.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3970886 : term264 = term125.
Proof. exact (@lem3970885 term140). Qed.
Lemma lem3970887 : term271 = term125.
Proof. exact (TRANS (@lem3970883) (@lem3970886)). Qed.
Lemma lem3970888 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970889 : term273 = term274.
Proof. exact (MK_COMB (@lem3970888) (@lem3970887)). Qed.
Lemma lem3970890 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem3970891 : term275 = term239.
Proof. exact (MK_COMB (@lem3970889) (@lem3970890)). Qed.
Lemma lem3970893 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3970894 : term239 = term125.
Proof. exact (@lem3970893 term140). Qed.
Lemma lem3970895 : term275 = term125.
Proof. exact (TRANS (@lem3970891) (@lem3970894)). Qed.
Lemma lem3970897 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970898 : term173 = term174.
Proof. exact (@lem3970897 term140 term140). Qed.
Lemma lem3970899 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970900 : term176 = term140.
Proof. exact (EQ_MP (@lem3970899) (@lem940073)). Qed.
Lemma lem3970901 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970902 : term174 = term139.
Proof. exact (MK_COMB (@lem3970901) (@lem3970900)). Qed.
Lemma lem3970903 : term173 = term139.
Proof. exact (TRANS (@lem3970898) (@lem3970902)). Qed.
Lemma lem3970904 : term274 = term274.
Proof. exact (eq_refl term274). Qed.
Lemma lem3970905 : term276 = term239.
Proof. exact (MK_COMB (@lem3970904) (@lem3970903)). Qed.
Lemma lem3970907 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3970908 : term239 = term125.
Proof. exact (@lem3970907 term140). Qed.
Lemma lem3970909 : term276 = term125.
Proof. exact (TRANS (@lem3970905) (@lem3970908)). Qed.
Lemma lem3970910 : term125 = term276.
Proof. exact (SYM (@lem3970909)). Qed.
Lemma lem3970911 : term275 = term276.
Proof. exact (TRANS (@lem3970895) (@lem3970910)). Qed.
Lemma lem3970912 : term265 = term161.
Proof. exact (@lem3970862 (@lem3970911)). Qed.
Lemma lem3970913 : term264 = term161.
Proof. exact (TRANS (@lem3970828) (@lem3970912)). Qed.
Lemma lem3970915 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3970916 : term161 = term125.
Proof. exact (@lem3970915 term125). Qed.
Lemma lem3970917 : term264 = term125.
Proof. exact (TRANS (@lem3970913) (@lem3970916)). Qed.
Lemma lem3970918 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970919 : term277 = term274.
Proof. exact (MK_COMB (@lem3970918) (@lem3970917)). Qed.
Lemma lem3970920 (_45800 : int) : (real_of_int _45800) = (real_of_int _45800).
Proof. exact (eq_refl (real_of_int _45800)). Qed.
Lemma lem3970921 (_45800 : int) : (term261 _45800) = (term278 _45800).
Proof. exact (MK_COMB (@lem3970919) (@lem3970920 _45800)). Qed.
Lemma lem3970922 (_45800 : int) : (term260 _45800) = (term278 _45800).
Proof. exact (TRANS (@lem3970819 _45800) (@lem3970921 _45800)). Qed.
Lemma lem3970923 (_45800 : int) : (term278 _45800) = term125.
Proof. exact (@lem1982719 (real_of_int _45800)). Qed.
Lemma lem3970924 (_45800 : int) : (term260 _45800) = term125.
Proof. exact (TRANS (@lem3970922 _45800) (@lem3970923 _45800)). Qed.
Lemma lem3970925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3970926 (_45800 : int) : (term279 _45800) = term280.
Proof. exact (MK_COMB (@lem3970925) (@lem3970924 _45800)). Qed.
Lemma lem3970927 (_45801 : int) (_45802 : int) : (term281 _45801 _45802) = (term282 _45801 _45802).
Proof. exact (@lem1982753 (term215 _45801) (real_of_int _45801) (real_of_int _45802) (term200 _45802)). Qed.
Lemma lem3970928 (_45801 : int) : (term260 _45801) = (term261 _45801).
Proof. exact (@lem1982713 term164 (real_of_int _45801)). Qed.
Lemma lem3970930 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3970931 : term139 = term190.
Proof. exact (@lem3970930 term140). Qed.
Lemma lem3970933 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3970934 : term164 = term165.
Proof. exact (@lem3970933 term140). Qed.
Lemma lem3970935 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3970936 : term262 = term263.
Proof. exact (MK_COMB (@lem3970935) (@lem3970934)). Qed.
Lemma lem3970937 : term264 = term265.
Proof. exact (MK_COMB (@lem3970936) (@lem3970931)). Qed.
Lemma lem3970938 : term266.
Proof. exact (@lem1981473 term164 term139 term139 term139 term125 term139). Qed.
Lemma lem3970940 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970941 : term228 = term234.
Proof. exact (@lem3970940 (NUMERAL 0) term140). Qed.
Lemma lem3970942 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970943 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970944 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970943 h1) (fun h1 : term234 = True => @lem3970942)). Qed.
Lemma lem3970945 : term234 = True.
Proof. exact (EQ_MP (@lem3970944) (@lem3970942)). Qed.
Lemma lem3970946 : term228 = True.
Proof. exact (TRANS (@lem3970941) (@lem3970945)). Qed.
Lemma lem3970947 : True = term228.
Proof. exact (SYM (@lem3970946)). Qed.
Lemma lem3970948 : term228.
Proof. exact (EQ_MP (@lem3970947) (@lem0)). Qed.
Lemma lem3970949 : term267.
Proof. exact (@lem3970938 (@lem3970948)). Qed.
Lemma lem3970951 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970952 : term228 = term234.
Proof. exact (@lem3970951 (NUMERAL 0) term140). Qed.
Lemma lem3970953 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970954 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970955 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970954 h1) (fun h1 : term234 = True => @lem3970953)). Qed.
Lemma lem3970956 : term234 = True.
Proof. exact (EQ_MP (@lem3970955) (@lem3970953)). Qed.
Lemma lem3970957 : term228 = True.
Proof. exact (TRANS (@lem3970952) (@lem3970956)). Qed.
Lemma lem3970958 : True = term228.
Proof. exact (SYM (@lem3970957)). Qed.
Lemma lem3970959 : term228.
Proof. exact (EQ_MP (@lem3970958) (@lem0)). Qed.
Lemma lem3970960 : term268.
Proof. exact (@lem3970949 (@lem3970959)). Qed.
Lemma lem3970962 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3970963 : term228 = term234.
Proof. exact (@lem3970962 (NUMERAL 0) term140). Qed.
Lemma lem3970964 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3970965 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3970966 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3970965 h1) (fun h1 : term234 = True => @lem3970964)). Qed.
Lemma lem3970967 : term234 = True.
Proof. exact (EQ_MP (@lem3970966) (@lem3970964)). Qed.
Lemma lem3970968 : term228 = True.
Proof. exact (TRANS (@lem3970963) (@lem3970967)). Qed.
Lemma lem3970969 : True = term228.
Proof. exact (SYM (@lem3970968)). Qed.
Lemma lem3970970 : term228.
Proof. exact (EQ_MP (@lem3970969) (@lem0)). Qed.
Lemma lem3970971 : term269.
Proof. exact (@lem3970960 (@lem3970970)). Qed.
Lemma lem3970973 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3970974 : term173 = term174.
Proof. exact (@lem3970973 term140 term140). Qed.
Lemma lem3970975 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970976 : term176 = term140.
Proof. exact (EQ_MP (@lem3970975) (@lem940073)). Qed.
Lemma lem3970977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970978 : term174 = term139.
Proof. exact (MK_COMB (@lem3970977) (@lem3970976)). Qed.
Lemma lem3970979 : term173 = term139.
Proof. exact (TRANS (@lem3970974) (@lem3970978)). Qed.
Lemma lem3970981 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3970982 : term191 = term196.
Proof. exact (@lem3970981 term140 term140). Qed.
Lemma lem3970983 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3970984 : term176 = term140.
Proof. exact (EQ_MP (@lem3970983) (@lem940073)). Qed.
Lemma lem3970985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3970986 : term174 = term139.
Proof. exact (MK_COMB (@lem3970985) (@lem3970984)). Qed.
Lemma lem3970987 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3970988 : term196 = term164.
Proof. exact (MK_COMB (@lem3970987) (@lem3970986)). Qed.
Lemma lem3970989 : term191 = term164.
Proof. exact (TRANS (@lem3970982) (@lem3970988)). Qed.
Lemma lem3970990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3970991 : term270 = term262.
Proof. exact (MK_COMB (@lem3970990) (@lem3970989)). Qed.
Lemma lem3970992 : term271 = term264.
Proof. exact (MK_COMB (@lem3970991) (@lem3970979)). Qed.
Lemma lem3970994 (m : nat) : (term272 m) = term125.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3970995 : term264 = term125.
Proof. exact (@lem3970994 term140). Qed.
Lemma lem3970996 : term271 = term125.
Proof. exact (TRANS (@lem3970992) (@lem3970995)). Qed.
Lemma lem3970997 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3970998 : term273 = term274.
Proof. exact (MK_COMB (@lem3970997) (@lem3970996)). Qed.
Lemma lem3970999 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem3971000 : term275 = term239.
Proof. exact (MK_COMB (@lem3970998) (@lem3970999)). Qed.
Lemma lem3971002 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3971003 : term239 = term125.
Proof. exact (@lem3971002 term140). Qed.
Lemma lem3971004 : term275 = term125.
Proof. exact (TRANS (@lem3971000) (@lem3971003)). Qed.
Lemma lem3971006 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3971007 : term173 = term174.
Proof. exact (@lem3971006 term140 term140). Qed.
Lemma lem3971008 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3971009 : term176 = term140.
Proof. exact (EQ_MP (@lem3971008) (@lem940073)). Qed.
Lemma lem3971010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3971011 : term174 = term139.
Proof. exact (MK_COMB (@lem3971010) (@lem3971009)). Qed.
Lemma lem3971012 : term173 = term139.
Proof. exact (TRANS (@lem3971007) (@lem3971011)). Qed.
Lemma lem3971013 : term274 = term274.
Proof. exact (eq_refl term274). Qed.
Lemma lem3971014 : term276 = term239.
Proof. exact (MK_COMB (@lem3971013) (@lem3971012)). Qed.
Lemma lem3971016 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3971017 : term239 = term125.
Proof. exact (@lem3971016 term140). Qed.
Lemma lem3971018 : term276 = term125.
Proof. exact (TRANS (@lem3971014) (@lem3971017)). Qed.
Lemma lem3971019 : term125 = term276.
Proof. exact (SYM (@lem3971018)). Qed.
Lemma lem3971020 : term275 = term276.
Proof. exact (TRANS (@lem3971004) (@lem3971019)). Qed.
Lemma lem3971021 : term265 = term161.
Proof. exact (@lem3970971 (@lem3971020)). Qed.
Lemma lem3971022 : term264 = term161.
Proof. exact (TRANS (@lem3970937) (@lem3971021)). Qed.
Lemma lem3971024 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3971025 : term161 = term125.
Proof. exact (@lem3971024 term125). Qed.
Lemma lem3971026 : term264 = term125.
Proof. exact (TRANS (@lem3971022) (@lem3971025)). Qed.
Lemma lem3971027 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3971028 : term277 = term274.
Proof. exact (MK_COMB (@lem3971027) (@lem3971026)). Qed.
Lemma lem3971029 (_45801 : int) : (real_of_int _45801) = (real_of_int _45801).
Proof. exact (eq_refl (real_of_int _45801)). Qed.
Lemma lem3971030 (_45801 : int) : (term261 _45801) = (term278 _45801).
Proof. exact (MK_COMB (@lem3971028) (@lem3971029 _45801)). Qed.
Lemma lem3971031 (_45801 : int) : (term260 _45801) = (term278 _45801).
Proof. exact (TRANS (@lem3970928 _45801) (@lem3971030 _45801)). Qed.
Lemma lem3971032 (_45801 : int) : (term278 _45801) = term125.
Proof. exact (@lem1982719 (real_of_int _45801)). Qed.
Lemma lem3971033 (_45801 : int) : (term260 _45801) = term125.
Proof. exact (TRANS (@lem3971031 _45801) (@lem3971032 _45801)). Qed.
Lemma lem3971034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3971035 (_45801 : int) : (term279 _45801) = term280.
Proof. exact (MK_COMB (@lem3971034) (@lem3971033 _45801)). Qed.
Lemma lem3971036 (_45802 : int) : (term283 _45802) = (term284 _45802).
Proof. exact (@lem1982763 (real_of_int _45802) (term215 _45802) term164). Qed.
Lemma lem3971037 (_45802 : int) : (term285 _45802) = (term261 _45802).
Proof. exact (@lem1982715 term164 (real_of_int _45802)). Qed.
Lemma lem3971039 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3971040 : term139 = term190.
Proof. exact (@lem3971039 term140). Qed.
Lemma lem3971042 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3971043 : term164 = term165.
Proof. exact (@lem3971042 term140). Qed.
Lemma lem3971044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3971045 : term262 = term263.
Proof. exact (MK_COMB (@lem3971044) (@lem3971043)). Qed.
Lemma lem3971046 : term264 = term265.
Proof. exact (MK_COMB (@lem3971045) (@lem3971040)). Qed.
Lemma lem3971047 : term266.
Proof. exact (@lem1981473 term164 term139 term139 term139 term125 term139). Qed.
Lemma lem3971049 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3971050 : term228 = term234.
Proof. exact (@lem3971049 (NUMERAL 0) term140). Qed.
Lemma lem3971051 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3971052 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3971053 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3971052 h1) (fun h1 : term234 = True => @lem3971051)). Qed.
Lemma lem3971054 : term234 = True.
Proof. exact (EQ_MP (@lem3971053) (@lem3971051)). Qed.
Lemma lem3971055 : term228 = True.
Proof. exact (TRANS (@lem3971050) (@lem3971054)). Qed.
Lemma lem3971056 : True = term228.
Proof. exact (SYM (@lem3971055)). Qed.
Lemma lem3971057 : term228.
Proof. exact (EQ_MP (@lem3971056) (@lem0)). Qed.
Lemma lem3971058 : term267.
Proof. exact (@lem3971047 (@lem3971057)). Qed.
Lemma lem3971060 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3971061 : term228 = term234.
Proof. exact (@lem3971060 (NUMERAL 0) term140). Qed.
Lemma lem3971062 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3971063 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3971064 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3971063 h1) (fun h1 : term234 = True => @lem3971062)). Qed.
Lemma lem3971065 : term234 = True.
Proof. exact (EQ_MP (@lem3971064) (@lem3971062)). Qed.
Lemma lem3971066 : term228 = True.
Proof. exact (TRANS (@lem3971061) (@lem3971065)). Qed.
Lemma lem3971067 : True = term228.
Proof. exact (SYM (@lem3971066)). Qed.
Lemma lem3971068 : term228.
Proof. exact (EQ_MP (@lem3971067) (@lem0)). Qed.
Lemma lem3971069 : term268.
Proof. exact (@lem3971058 (@lem3971068)). Qed.
Lemma lem3971071 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3971072 : term228 = term234.
Proof. exact (@lem3971071 (NUMERAL 0) term140). Qed.
Lemma lem3971073 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3971074 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3971075 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3971074 h1) (fun h1 : term234 = True => @lem3971073)). Qed.
Lemma lem3971076 : term234 = True.
Proof. exact (EQ_MP (@lem3971075) (@lem3971073)). Qed.
Lemma lem3971077 : term228 = True.
Proof. exact (TRANS (@lem3971072) (@lem3971076)). Qed.
Lemma lem3971078 : True = term228.
Proof. exact (SYM (@lem3971077)). Qed.
Lemma lem3971079 : term228.
Proof. exact (EQ_MP (@lem3971078) (@lem0)). Qed.
Lemma lem3971080 : term269.
Proof. exact (@lem3971069 (@lem3971079)). Qed.
Lemma lem3971082 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3971083 : term173 = term174.
Proof. exact (@lem3971082 term140 term140). Qed.
Lemma lem3971084 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3971085 : term176 = term140.
Proof. exact (EQ_MP (@lem3971084) (@lem940073)). Qed.
Lemma lem3971086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3971087 : term174 = term139.
Proof. exact (MK_COMB (@lem3971086) (@lem3971085)). Qed.
Lemma lem3971088 : term173 = term139.
Proof. exact (TRANS (@lem3971083) (@lem3971087)). Qed.
Lemma lem3971090 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3971091 : term191 = term196.
Proof. exact (@lem3971090 term140 term140). Qed.
Lemma lem3971092 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3971093 : term176 = term140.
Proof. exact (EQ_MP (@lem3971092) (@lem940073)). Qed.
Lemma lem3971094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3971095 : term174 = term139.
Proof. exact (MK_COMB (@lem3971094) (@lem3971093)). Qed.
Lemma lem3971096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3971097 : term196 = term164.
Proof. exact (MK_COMB (@lem3971096) (@lem3971095)). Qed.
Lemma lem3971098 : term191 = term164.
Proof. exact (TRANS (@lem3971091) (@lem3971097)). Qed.
Lemma lem3971099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3971100 : term270 = term262.
Proof. exact (MK_COMB (@lem3971099) (@lem3971098)). Qed.
Lemma lem3971101 : term271 = term264.
Proof. exact (MK_COMB (@lem3971100) (@lem3971088)). Qed.
Lemma lem3971103 (m : nat) : (term272 m) = term125.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3971104 : term264 = term125.
Proof. exact (@lem3971103 term140). Qed.
Lemma lem3971105 : term271 = term125.
Proof. exact (TRANS (@lem3971101) (@lem3971104)). Qed.
Lemma lem3971106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3971107 : term273 = term274.
Proof. exact (MK_COMB (@lem3971106) (@lem3971105)). Qed.
Lemma lem3971108 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem3971109 : term275 = term239.
Proof. exact (MK_COMB (@lem3971107) (@lem3971108)). Qed.
Lemma lem3971111 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3971112 : term239 = term125.
Proof. exact (@lem3971111 term140). Qed.
Lemma lem3971113 : term275 = term125.
Proof. exact (TRANS (@lem3971109) (@lem3971112)). Qed.
Lemma lem3971115 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3971116 : term173 = term174.
Proof. exact (@lem3971115 term140 term140). Qed.
Lemma lem3971117 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3971118 : term176 = term140.
Proof. exact (EQ_MP (@lem3971117) (@lem940073)). Qed.
Lemma lem3971119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3971120 : term174 = term139.
Proof. exact (MK_COMB (@lem3971119) (@lem3971118)). Qed.
Lemma lem3971121 : term173 = term139.
Proof. exact (TRANS (@lem3971116) (@lem3971120)). Qed.
Lemma lem3971122 : term274 = term274.
Proof. exact (eq_refl term274). Qed.
Lemma lem3971123 : term276 = term239.
Proof. exact (MK_COMB (@lem3971122) (@lem3971121)). Qed.
Lemma lem3971125 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3971126 : term239 = term125.
Proof. exact (@lem3971125 term140). Qed.
Lemma lem3971127 : term276 = term125.
Proof. exact (TRANS (@lem3971123) (@lem3971126)). Qed.
Lemma lem3971128 : term125 = term276.
Proof. exact (SYM (@lem3971127)). Qed.
Lemma lem3971129 : term275 = term276.
Proof. exact (TRANS (@lem3971113) (@lem3971128)). Qed.
Lemma lem3971130 : term265 = term161.
Proof. exact (@lem3971080 (@lem3971129)). Qed.
Lemma lem3971131 : term264 = term161.
Proof. exact (TRANS (@lem3971046) (@lem3971130)). Qed.
Lemma lem3971133 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3971134 : term161 = term125.
Proof. exact (@lem3971133 term125). Qed.
Lemma lem3971135 : term264 = term125.
Proof. exact (TRANS (@lem3971131) (@lem3971134)). Qed.
Lemma lem3971136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3971137 : term277 = term274.
Proof. exact (MK_COMB (@lem3971136) (@lem3971135)). Qed.
Lemma lem3971138 (_45802 : int) : (real_of_int _45802) = (real_of_int _45802).
Proof. exact (eq_refl (real_of_int _45802)). Qed.
Lemma lem3971139 (_45802 : int) : (term261 _45802) = (term278 _45802).
Proof. exact (MK_COMB (@lem3971137) (@lem3971138 _45802)). Qed.
Lemma lem3971140 (_45802 : int) : (term285 _45802) = (term278 _45802).
Proof. exact (TRANS (@lem3971037 _45802) (@lem3971139 _45802)). Qed.
Lemma lem3971141 (_45802 : int) : (term278 _45802) = term125.
Proof. exact (@lem1982719 (real_of_int _45802)). Qed.
Lemma lem3971142 (_45802 : int) : (term285 _45802) = term125.
Proof. exact (TRANS (@lem3971140 _45802) (@lem3971141 _45802)). Qed.
Lemma lem3971143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3971144 (_45802 : int) : (term286 _45802) = term280.
Proof. exact (MK_COMB (@lem3971143) (@lem3971142 _45802)). Qed.
Lemma lem3971145 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem3971146 (_45802 : int) : (term284 _45802) = term287.
Proof. exact (MK_COMB (@lem3971144 _45802) (@lem3971145)). Qed.
Lemma lem3971147 (_45802 : int) : (term283 _45802) = term287.
Proof. exact (TRANS (@lem3971036 _45802) (@lem3971146 _45802)). Qed.
Lemma lem3971148 : term287 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem3971149 (_45802 : int) : (term283 _45802) = term164.
Proof. exact (TRANS (@lem3971147 _45802) (@lem3971148)). Qed.
Lemma lem3971150 (_45801 : int) (_45802 : int) : (term282 _45801 _45802) = term287.
Proof. exact (MK_COMB (@lem3971035 _45801) (@lem3971149 _45802)). Qed.
Lemma lem3971151 (_45801 : int) (_45802 : int) : (term281 _45801 _45802) = term287.
Proof. exact (TRANS (@lem3970927 _45801 _45802) (@lem3971150 _45801 _45802)). Qed.
Lemma lem3971152 : term287 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem3971153 (_45801 : int) (_45802 : int) : (term281 _45801 _45802) = term164.
Proof. exact (TRANS (@lem3971151 _45801 _45802) (@lem3971152)). Qed.
Lemma lem3971154 (_45800 : int) (_45801 : int) (_45802 : int) : (term258 _45800 _45801 _45802) = term287.
Proof. exact (MK_COMB (@lem3970926 _45800) (@lem3971153 _45801 _45802)). Qed.
Lemma lem3971155 (_45800 : int) (_45801 : int) (_45802 : int) : (term257 _45800 _45801 _45802) = term287.
Proof. exact (TRANS (@lem3970818 _45800 _45801 _45802) (@lem3971154 _45800 _45801 _45802)). Qed.
Lemma lem3971156 : term287 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem3971157 (_45800 : int) (_45801 : int) (_45802 : int) : (term257 _45800 _45801 _45802) = term164.
Proof. exact (TRANS (@lem3971155 _45800 _45801 _45802) (@lem3971156)). Qed.
Lemma lem3971158 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3971159 (_45800 : int) (_45801 : int) (_45802 : int) : (term288 _45800 _45801 _45802) = term289.
Proof. exact (MK_COMB (@lem3971158) (@lem3971157 _45800 _45801 _45802)). Qed.
Lemma lem3971160 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem3971161 (_45800 : int) (_45801 : int) (_45802 : int) : (term256 _45800 _45801 _45802) = term290.
Proof. exact (MK_COMB (@lem3971159 _45800 _45801 _45802) (@lem3971160)). Qed.
Lemma lem3971162 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term290.
Proof. exact (EQ_MP (@lem3971161 _45800 _45801 _45802) (@lem3970817 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3971164 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3971165 : term290 = term291.
Proof. exact (@lem3971164 term125 term164). Qed.
Lemma lem3971167 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3971168 : term164 = term165.
Proof. exact (@lem3971167 term140). Qed.
Lemma lem3971170 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3971171 : term125 = term161.
Proof. exact (@lem3971170 (NUMERAL 0)). Qed.
Lemma lem3971172 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3971173 : term127 = term292.
Proof. exact (MK_COMB (@lem3971172) (@lem3971171)). Qed.
Lemma lem3971174 : term291 = term293.
Proof. exact (MK_COMB (@lem3971173) (@lem3971168)). Qed.
Lemma lem3971175 : term294.
Proof. exact (@lem1980026 term125 term139 term164 term139). Qed.
Lemma lem3971177 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3971178 : term228 = term234.
Proof. exact (@lem3971177 (NUMERAL 0) term140). Qed.
Lemma lem3971179 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3971180 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3971181 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3971180 h1) (fun h1 : term234 = True => @lem3971179)). Qed.
Lemma lem3971182 : term234 = True.
Proof. exact (EQ_MP (@lem3971181) (@lem3971179)). Qed.
Lemma lem3971183 : term228 = True.
Proof. exact (TRANS (@lem3971178) (@lem3971182)). Qed.
Lemma lem3971184 : True = term228.
Proof. exact (SYM (@lem3971183)). Qed.
Lemma lem3971185 : term228.
Proof. exact (EQ_MP (@lem3971184) (@lem0)). Qed.
Lemma lem3971186 : term295.
Proof. exact (@lem3971175 (@lem3971185)). Qed.
Lemma lem3971188 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3971189 : term228 = term234.
Proof. exact (@lem3971188 (NUMERAL 0) term140). Qed.
Lemma lem3971190 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3971191 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3971192 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3971191 h1) (fun h1 : term234 = True => @lem3971190)). Qed.
Lemma lem3971193 : term234 = True.
Proof. exact (EQ_MP (@lem3971192) (@lem3971190)). Qed.
Lemma lem3971194 : term228 = True.
Proof. exact (TRANS (@lem3971189) (@lem3971193)). Qed.
Lemma lem3971195 : True = term228.
Proof. exact (SYM (@lem3971194)). Qed.
Lemma lem3971196 : term228.
Proof. exact (EQ_MP (@lem3971195) (@lem0)). Qed.
Lemma lem3971197 : term293 = term296.
Proof. exact (@lem3971186 (@lem3971196)). Qed.
Lemma lem3971199 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3971200 : term191 = term196.
Proof. exact (@lem3971199 term140 term140). Qed.
Lemma lem3971201 : (term175 = (BIT1 0)) = (term176 = term140).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3971202 : term176 = term140.
Proof. exact (EQ_MP (@lem3971201) (@lem940073)). Qed.
Lemma lem3971203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3971204 : term174 = term139.
Proof. exact (MK_COMB (@lem3971203) (@lem3971202)). Qed.
Lemma lem3971205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3971206 : term196 = term164.
Proof. exact (MK_COMB (@lem3971205) (@lem3971204)). Qed.
Lemma lem3971207 : term191 = term164.
Proof. exact (TRANS (@lem3971200) (@lem3971206)). Qed.
Lemma lem3971209 (x : nat) : (term238 x) = term125.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3971210 : term239 = term125.
Proof. exact (@lem3971209 term140). Qed.
Lemma lem3971211 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3971212 : term297 = term127.
Proof. exact (MK_COMB (@lem3971211) (@lem3971210)). Qed.
Lemma lem3971213 : term296 = term291.
Proof. exact (MK_COMB (@lem3971212) (@lem3971207)). Qed.
Lemma lem3971215 (m : nat) (n : nat) : (term298 m n) = (term299 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3971216 : term291 = term300.
Proof. exact (@lem3971215 (NUMERAL 0) term140). Qed.
Lemma lem3971217 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3971218 (h1 : term235 = (BIT1 0)) : (term140 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3971219 : (term235 = (BIT1 0)) = ((term140 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem3971218 h1) (fun h1 : (term140 = (NUMERAL 0)) = False => @lem3971217)). Qed.
Lemma lem3971220 : (term140 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3971219) (@lem3971217)). Qed.
Lemma lem3971221 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3971222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3971223 : term301 = (and True).
Proof. exact (MK_COMB (@lem3971222) (@lem3971221)). Qed.
Lemma lem3971224 : term300 = (True /\ False).
Proof. exact (MK_COMB (@lem3971223) (@lem3971220)). Qed.
Lemma lem3971226 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3971227 : term300 = False.
Proof. exact (TRANS (@lem3971224) (@lem3971226)). Qed.
Lemma lem3971228 : term291 = False.
Proof. exact (TRANS (@lem3971216) (@lem3971227)). Qed.
Lemma lem3971229 : term296 = False.
Proof. exact (TRANS (@lem3971213) (@lem3971228)). Qed.
Lemma lem3971230 : term293 = False.
Proof. exact (TRANS (@lem3971197) (@lem3971229)). Qed.
Lemma lem3971231 : term291 = False.
Proof. exact (TRANS (@lem3971174) (@lem3971230)). Qed.
Lemma lem3971232 : term290 = False.
Proof. exact (TRANS (@lem3971165) (@lem3971231)). Qed.
Lemma lem3971233 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : False.
Proof. exact (EQ_MP (@lem3971232) (@lem3971162 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3971235 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : term226 _101508 s t _45800 _45801 _45802.
Proof. exact (h1). Qed.
Lemma lem3971236 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : (term226 _101508 s t _45800 _45801 _45802) = False.
Proof. exact (prop_ext (fun h2 : term226 _101508 s t _45800 _45801 _45802 => @lem3971233 _101508 s t _45800 _45801 _45802 h1) (fun h2 : False => @lem3971235 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3971237 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45800 : int) (_45801 : int) (_45802 : int) (h1 : term226 _101508 s t _45800 _45801 _45802) : False.
Proof. exact (EQ_MP (@lem3971236 _101508 s t _45800 _45801 _45802 h1) (@lem3971235 _101508 s t _45800 _45801 _45802 h1)). Qed.
Lemma lem3971238 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) (h1 : term156 _101508 s t _45802 _45800 _45801) : term156 _101508 s t _45802 _45800 _45801.
Proof. exact (h1). Qed.
Lemma lem3971239 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) (h1 : term156 _101508 s t _45802 _45800 _45801) : term226 _101508 s t _45800 _45801 _45802.
Proof. exact (EQ_MP (@lem3970709 _101508 s t _45800 _45801 _45802) (@lem3971238 _101508 s t _45802 _45800 _45801 h1)). Qed.
Lemma lem3971240 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) (h1 : term156 _101508 s t _45802 _45800 _45801) : (term226 _101508 s t _45800 _45801 _45802) = False.
Proof. exact (prop_ext (fun h2 : term226 _101508 s t _45800 _45801 _45802 => @lem3971237 _101508 s t _45800 _45801 _45802 h2) (fun h2 : False => @lem3971239 _101508 s t _45802 _45800 _45801 h1)). Qed.
Lemma lem3971241 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) (h1 : term156 _101508 s t _45802 _45800 _45801) : False.
Proof. exact (EQ_MP (@lem3971240 _101508 s t _45802 _45800 _45801 h1) (@lem3971239 _101508 s t _45802 _45800 _45801 h1)). Qed.
Lemma lem3971242 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : term302 _101508 s t _45802 _45800 _45801.
Proof. exact (fun h0 : term156 _101508 s t _45802 _45800 _45801 => @lem3971241 _101508 s t _45802 _45800 _45801 h0). Qed.
Lemma lem3971243 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : term303 _101508 s t _45802 _45800 _45801.
Proof. exact (@lem1386578 (term304 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3971246 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : term304 _101508 s t _45802 _45800 _45801.
Proof. exact (@lem3971243 _101508 s t _45802 _45800 _45801 (@lem3971242 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3971247 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term154 _101508 s t _45802 _45800 _45801) = (term118 _101508 s t _45802 _45800 _45801).
Proof. exact (SYM (@lem3970318 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3971248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3971249 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : (term304 _101508 s t _45802 _45800 _45801) = (term83 _101508 s t _45802 _45800 _45801).
Proof. exact (MK_COMB (@lem3971248) (@lem3971247 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3971250 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : term83 _101508 s t _45802 _45800 _45801.
Proof. exact (EQ_MP (@lem3971249 _101508 s t _45802 _45800 _45801) (@lem3971246 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3971251 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) (_45802 : int) (_45800 : int) (_45801 : int) : term84 _101508 s t _45802 _45800 _45801.
Proof. exact (EQ_MP (@lem3970129 _101508 s t _45802 _45800 _45801) (@lem3971250 _101508 s t _45802 _45800 _45801)). Qed.
Lemma lem3971252 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term305 _101508 s t.
Proof. exact (@lem3971251 _101508 s t (term71 _101508 s t) (term306 _101508 s) (term306 _101508 t)). Qed.
Lemma lem3971253 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term307 _101508 s t.
Proof. exact (@lem3971252 _101508 s t (@lem3970122 _101508 s)). Qed.
Lemma lem3971254 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term308 _101508 s t.
Proof. exact (@lem3971253 _101508 s t (@lem3970125 _101508 t)). Qed.
Lemma lem3971255 {_101508 : Type'} (s : _101508 -> Prop) (t : _101508 -> Prop) : term74 _101508 s t.
Proof. exact (@lem3971254 _101508 s t (@lem3970128 _101508 s t)). Qed.
Lemma lem3971256 {_101508 : Type'} (s : _101508 -> Prop) : term76 _101508 s.
Proof. exact (fun t : _101508 -> Prop => @lem3971255 _101508 s t). Qed.
Lemma lem3971257 {_101508 : Type'} : term78 _101508.
Proof. exact (fun s : _101508 -> Prop => @lem3971256 _101508 s). Qed.
Lemma lem3971258 {_101508 : Type'} : (term78 _101508) = (term42 _101508).
Proof. exact (SYM (@lem3970119 _101508)). Qed.
Lemma lem3971259 {_101508 : Type'} : term42 _101508.
Proof. exact (EQ_MP (@lem3971258 _101508) (@lem3971257 _101508)). Qed.
Lemma lem3971260 {_101508 : Type'} : (term42 _101508) = ((term42 _101508) = True).
Proof. exact (@lem7 (term42 _101508)). Qed.
Lemma lem3971261 {_101508 : Type'} : (term42 _101508) = True.
Proof. exact (EQ_MP (@lem3971260 _101508) (@lem3971259 _101508)). Qed.
Lemma lem3971262 {_101508 : Type'} : True = (term42 _101508).
Proof. exact (SYM (@lem3971261 _101508)). Qed.
Lemma lem3971263 {_101508 : Type'} : term42 _101508.
Proof. exact (EQ_MP (@lem3971262 _101508) (@lem0)). Qed.
Lemma lem3971264 {_101508 : Type'} : term41 _101508.
Proof. exact (EQ_MP (@lem3969936 _101508) (@lem3971263 _101508)). Qed.
