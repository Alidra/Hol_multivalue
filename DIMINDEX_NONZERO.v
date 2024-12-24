Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_NONZERO_term_abbrevs.
Require Import CARD_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1855_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Lemma lem7590242 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7590243 {A : Type'} (s : A -> Prop) : (term0 A s) = ((@dimindex A s) = (term1 A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7590248 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (EQ_MP (@lem7590243 A s) (@lem7590242 A s)). Qed.
Lemma lem7590249 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (@lem7590248 A s). Qed.
Lemma lem7590250 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7590251 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A).
Proof. exact (MK_COMB (@lem7590250) (@lem7590249 A s)). Qed.
Lemma lem7590252 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7590253 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (NUMERAL 0)) = ((term1 A) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7590251 A s) (@lem7590252)). Qed.
Lemma lem7590256 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7590257 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A).
Proof. exact (MK_COMB (@lem7590256) (@lem7590253 A s)). Qed.
Lemma lem7590258 {A : Type'} (s : A -> Prop) : (term5 A) = (term4 A s).
Proof. exact (SYM (@lem7590257 A s)). Qed.
Lemma lem7590259 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term6 _476 _475 _474 _477) = (term7 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem7590260 (_474 : nat) (_475 : Prop) (_477 : nat) : (term8 _475 _474 _477) = (term9 _474 _475 _477).
Proof. exact (@lem7590259 _474 _475 term10 _477). Qed.
Lemma lem7590261 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem7590260 (@CARD A (@UNIV A)) (@FINITE A (@UNIV A)) term13). Qed.
Lemma lem7590262 : term14 = term15.
Proof. exact (eq_refl term14). Qed.
Lemma lem7590263 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem7590264 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem7590263 A) (@lem7590262)). Qed.
Lemma lem7590265 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7590266 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem7590267 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem7590266 A) (@lem7590265 A)). Qed.
Lemma lem7590268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7590269 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem7590268) (@lem7590267 A)). Qed.
Lemma lem7590270 {A : Type'} : (term12 A) = (term26 A).
Proof. exact (MK_COMB (@lem7590269 A) (@lem7590264 A)). Qed.
Lemma lem7590271 {A : Type'} : (term11 A) = (term5 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem7590272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7590273 {A : Type'} : (term27 A) = (term28 A).
Proof. exact (MK_COMB (@lem7590272) (@lem7590271 A)). Qed.
Lemma lem7590274 {A : Type'} : ((term11 A) = (term12 A)) = ((term5 A) = (term26 A)).
Proof. exact (MK_COMB (@lem7590273 A) (@lem7590270 A)). Qed.
Lemma lem7590275 {A : Type'} : (term5 A) = (term26 A).
Proof. exact (EQ_MP (@lem7590274 A) (@lem7590261 A)). Qed.
Lemma lem7590276 {A : Type'} : (term26 A) = (term5 A).
Proof. exact (SYM (@lem7590275 A)). Qed.
Lemma lem7590277 {A : Type'} (h1 : @FINITE A (@UNIV A)) : @FINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem7590955 {_99911 : Type'} (s : _99911 -> Prop) : term29 _99911 s.
Proof. exact (@lem3854502 _99911 s). Qed.
Lemma lem7590956 {_99911 : Type'} (s : _99911 -> Prop) : (term29 _99911 s) = (term30 _99911 s).
Proof. exact (eq_refl (term29 _99911 s)). Qed.
Lemma lem7590957 {_99911 : Type'} (s : _99911 -> Prop) : term30 _99911 s.
Proof. exact (EQ_MP (@lem7590956 _99911 s) (@lem7590955 _99911 s)). Qed.
Lemma lem7590958 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : @FINITE _99911 s.
Proof. exact (h1). Qed.
Lemma lem7590959 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : ((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911)).
Proof. exact (@lem7590957 _99911 s (@lem7590958 _99911 s h1)). Qed.
Lemma lem7590965 {A : Type'} : (@FINITE A (@UNIV A)) = ((@FINITE A (@UNIV A)) = True).
Proof. exact (@lem7 (@FINITE A (@UNIV A))). Qed.
Lemma lem7590968 {_99911 : Type'} (s : _99911 -> Prop) : term30 _99911 s.
Proof. exact (fun h0 : @FINITE _99911 s => @lem7590959 _99911 s h0). Qed.
Lemma lem7590969 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (@lem7590968 A s). Qed.
Lemma lem7590970 {A : Type'} : term31 A.
Proof. exact (@lem7590969 A (@UNIV A)). Qed.
Lemma lem7590972 {A : Type'} (h1 : @FINITE A (@UNIV A)) : (@FINITE A (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7590965 A) (@lem7590277 A h1)). Qed.
Lemma lem7590973 {A : Type'} (h1 : @FINITE A (@UNIV A)) : True = (@FINITE A (@UNIV A)).
Proof. exact (SYM (@lem7590972 A h1)). Qed.
Lemma lem7590974 {A : Type'} (h1 : @FINITE A (@UNIV A)) : @FINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem7590973 A h1) (@lem0)). Qed.
Lemma lem7590975 {A : Type'} (h1 : @FINITE A (@UNIV A)) : ((@CARD A (@UNIV A)) = (NUMERAL 0)) = ((@UNIV A) = (@EMPTY A)).
Proof. exact (@lem7590970 A (@lem7590974 A h1)). Qed.
Lemma lem7590978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7590979 {A : Type'} (h1 : @FINITE A (@UNIV A)) : (term20 A) = (term32 A).
Proof. exact (MK_COMB (@lem7590978) (@lem7590975 A h1)). Qed.
Lemma lem7590982 {A : Type'} (h1 : @FINITE A (@UNIV A)) : (term32 A) = (term20 A).
Proof. exact (SYM (@lem7590979 A h1)). Qed.
Lemma lem7591316 : term33.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem7591317 : term34.
Proof. exact (proj2 (@lem7591316)). Qed.
Lemma lem7591318 : term35.
Proof. exact (proj2 (@lem7591317)). Qed.
Lemma lem7591319 : term36.
Proof. exact (proj2 (@lem7591318)). Qed.
Lemma lem7591361 : term37.
Proof. exact (proj1 (@lem7591319)). Qed.
Lemma lem7591362 (n : nat) : term38 n.
Proof. exact (@lem7591361 n). Qed.
Lemma lem7591363 (n : nat) : (term38 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem7591370 : term39.
Proof. exact (proj1 (@lem7591316)). Qed.
Lemma lem7591371 (m : nat) : term40 m.
Proof. exact (@lem7591370 m). Qed.
Lemma lem7591372 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem7591373 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem7591372 m) (@lem7591371 m)). Qed.
Lemma lem7591374 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem7591373 m n). Qed.
Lemma lem7591375 (m : nat) (n : nat) : (term42 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem7591640 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem7591375 m n) (@lem7591374 m n)). Qed.
Lemma lem7591641 : (term13 = (NUMERAL 0)) = ((BIT1 0) = 0).
Proof. exact (@lem7591640 (BIT1 0) 0). Qed.
Lemma lem7591643 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem7591363 n) (@lem7591362 n)). Qed.
Lemma lem7591644 : ((BIT1 0) = 0) = False.
Proof. exact (@lem7591643 0). Qed.
Lemma lem7591645 : (term13 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem7591641) (@lem7591644)). Qed.
Lemma lem7591646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7591647 : term15 = (~ False).
Proof. exact (MK_COMB (@lem7591646) (@lem7591645)). Qed.
Lemma lem7591649 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7591650 : term15 = True.
Proof. exact (TRANS (@lem7591647) (@lem7591649)). Qed.
Lemma lem7591651 : True = term15.
Proof. exact (SYM (@lem7591650)). Qed.
Lemma lem7591656 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term43 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7591657 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term43 A s t).
Proof. exact (@lem7591656 A s t). Qed.
Lemma lem7591658 {A : Type'} : ((@UNIV A) = (@EMPTY A)) = (term44 A).
Proof. exact (@lem7591657 A (@UNIV A) (@EMPTY A)). Qed.
Lemma lem7591667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7591668 {A : Type'} : (term32 A) = (term45 A).
Proof. exact (MK_COMB (@lem7591667) (@lem7591658 A)). Qed.
Lemma lem7591669 {A : Type'} : (term45 A) = (term32 A).
Proof. exact (SYM (@lem7591668 A)). Qed.
Lemma lem7591677 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem7591678 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem7591677 A x). Qed.
Lemma lem7591679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7591680 {A : Type'} (x : A) : (term46 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7591679) (@lem7591678 A x)). Qed.
Lemma lem7591682 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7591683 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7591682 A x). Qed.
Lemma lem7591684 {A : Type'} (x : A) : ((@IN A x (@UNIV A)) = (@IN A x (@EMPTY A))) = (True = False).
Proof. exact (MK_COMB (@lem7591680 A x) (@lem7591683 A x)). Qed.
Lemma lem7591686 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7591687 : (True = False) = False.
Proof. exact (@lem7591686 False). Qed.
Lemma lem7591688 {A : Type'} (x : A) : ((@IN A x (@UNIV A)) = (@IN A x (@EMPTY A))) = False.
Proof. exact (TRANS (@lem7591684 A x) (@lem7591687)). Qed.
Lemma lem7591689 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (fun_ext (fun x : A => @lem7591688 A x)). Qed.
Lemma lem7591690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7591691 {A : Type'} : (term44 A) = (term49 A).
Proof. exact (MK_COMB (@lem7591690 A) (@lem7591689 A)). Qed.
Lemma lem7591693 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7591694 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (@lem7591693 A t). Qed.
Lemma lem7591695 {A : Type'} : (term49 A) = False.
Proof. exact (@lem7591694 A False). Qed.
Lemma lem7591696 {A : Type'} : (term44 A) = False.
Proof. exact (TRANS (@lem7591691 A) (@lem7591695 A)). Qed.
Lemma lem7591697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7591698 {A : Type'} : (term45 A) = (~ False).
Proof. exact (MK_COMB (@lem7591697) (@lem7591696 A)). Qed.
Lemma lem7591700 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7591701 {A : Type'} : (term45 A) = True.
Proof. exact (TRANS (@lem7591698 A) (@lem7591700)). Qed.
Lemma lem7591702 {A : Type'} : True = (term45 A).
Proof. exact (SYM (@lem7591701 A)). Qed.
Lemma lem7591703 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem7591702 A) (@lem0)). Qed.
Lemma lem7591704 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem7591669 A) (@lem7591703 A)). Qed.
Lemma lem7591706 : term15.
Proof. exact (EQ_MP (@lem7591651) (@lem0)). Qed.
Lemma lem7591707 {A : Type'} : term18 A.
Proof. exact (fun h0 : term51 A => @lem7591706). Qed.
Lemma lem7591708 {A : Type'} (h1 : @FINITE A (@UNIV A)) : term20 A.
Proof. exact (EQ_MP (@lem7590982 A h1) (@lem7591704 A)). Qed.
Lemma lem7591709 {A : Type'} (h1 : @FINITE A (@UNIV A)) : (@FINITE A (@UNIV A)) = (term20 A).
Proof. exact (prop_ext (fun h2 : @FINITE A (@UNIV A) => @lem7591708 A h1) (fun h2 : term20 A => @lem7590277 A h1)). Qed.
Lemma lem7591710 {A : Type'} (h1 : @FINITE A (@UNIV A)) : term20 A.
Proof. exact (EQ_MP (@lem7591709 A h1) (@lem7590277 A h1)). Qed.
Lemma lem7591711 {A : Type'} : term23 A.
Proof. exact (fun h0 : @FINITE A (@UNIV A) => @lem7591710 A h0). Qed.
Lemma lem7591712 {A : Type'} : term26 A.
Proof. exact (conj (@lem7591711 A) (@lem7591707 A)). Qed.
Lemma lem7591713 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem7590276 A) (@lem7591712 A)). Qed.
Lemma lem7591714 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem7590258 A s) (@lem7591713 A)). Qed.
Lemma lem7591719 {A : Type'} : term52 A.
Proof. exact (fun s : A -> Prop => @lem7591714 A s). Qed.
