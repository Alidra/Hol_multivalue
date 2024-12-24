Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_CASES_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm18394_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem75647 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem75648 : term1.
Proof. exact (@lem75647 term2). Qed.
Lemma lem75649 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem75650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem75651 : term5 = term6.
Proof. exact (MK_COMB (@lem75650) (@lem75649)). Qed.
Lemma lem75652 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem75653 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem75654 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem75653) (@lem75652 m)). Qed.
Lemma lem75655 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem75656 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem75654 m) (@lem75655 m)). Qed.
Lemma lem75657 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem75656 m)). Qed.
Lemma lem75658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75659 : term17 = term18.
Proof. exact (MK_COMB (@lem75658) (@lem75657)). Qed.
Lemma lem75660 : term19 = term20.
Proof. exact (MK_COMB (@lem75651) (@lem75659)). Qed.
Lemma lem75661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem75662 : term21 = term22.
Proof. exact (MK_COMB (@lem75661) (@lem75660)). Qed.
Lemma lem75663 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem75664 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem75663 m)). Qed.
Lemma lem75665 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75666 : term24 = term25.
Proof. exact (MK_COMB (@lem75665) (@lem75664)). Qed.
Lemma lem75667 : term1 = term26.
Proof. exact (MK_COMB (@lem75662) (@lem75666)). Qed.
Lemma lem75668 : term26.
Proof. exact (EQ_MP (@lem75667) (@lem75648)). Qed.
Lemma lem75671 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem75672 : term4 = term28.
Proof. exact (@lem75671 term4). Qed.
Lemma lem75673 : term28 = term4.
Proof. exact (SYM (@lem75672)). Qed.
Lemma lem75674 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem75677 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem75678 : term30.
Proof. exact (fun h0 : term28 => @lem75677 h0). Qed.
Lemma lem75679 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem75680 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem75681 (h1 : term28) (h2 : term30) : term28.
Proof. exact (@lem75679 h2 (@lem75680 h1)). Qed.
Lemma lem75682 (h1 : term28) : term31.
Proof. exact (fun h0 : term30 => @lem75681 h1 h0). Qed.
Lemma lem75683 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem75684 (h1 : term28) (h2 : term30) : term28.
Proof. exact (@lem75682 h1 (@lem75683 h2)). Qed.
Lemma lem75685 (h1 : term30) : term30.
Proof. exact (fun h0 : term28 => @lem75684 h0 h1). Qed.
Lemma lem75686 : term32.
Proof. exact (fun h0 : term30 => @lem75685 h0). Qed.
Lemma lem75689 : term30.
Proof. exact (@lem75686 (@lem75678)). Qed.
Lemma lem75691 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem75692 : term28 = term33.
Proof. exact (@lem75691 term29). Qed.
Lemma lem75694 (t : Prop) : (term34 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem75695 : term33 = term4.
Proof. exact (@lem75694 term4). Qed.
Lemma lem75706 : term28 = term4.
Proof. exact (TRANS (@lem75692) (@lem75695)). Qed.
Lemma lem75707 (n : nat) : ((NUMERAL 0) = (S n)) = ((NUMERAL 0) = (S n)).
Proof. exact (eq_refl ((NUMERAL 0) = (S n))). Qed.
Lemma lem75708 : term35 = term35.
Proof. exact (fun_ext (fun n : nat => @lem75707 n)). Qed.
Lemma lem75709 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem75710 : term36 = term36.
Proof. exact (MK_COMB (@lem75709) (@lem75708)). Qed.
Lemma lem75713 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem75714 : term4 = term4.
Proof. exact (MK_COMB (@lem75713) (@lem75710)). Qed.
Lemma lem75725 : term28 = term4.
Proof. exact (TRANS (@lem75706) (@lem75714)). Qed.
Lemma lem75726 : term4 = term28.
Proof. exact (SYM (@lem75725)). Qed.
Lemma lem75728 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem75729 : term4 = term28.
Proof. exact (@lem75728 term4). Qed.
Lemma lem75730 : term28 = term4.
Proof. exact (SYM (@lem75729)). Qed.
Lemma lem75731 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem75734 (P : nat -> Prop) : (term38 P) = (term39 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem75735 : term40 = term41.
Proof. exact (@lem75734 term35). Qed.
Lemma lem75736 (n : nat) : (term42 n) = ((NUMERAL 0) = (S n)).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem75737 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem75739 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem75737) (@lem75736 n)). Qed.
Lemma lem75740 : term45 = term46.
Proof. exact (fun_ext (fun n : nat => @lem75739 n)). Qed.
Lemma lem75741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75742 : term41 = term47.
Proof. exact (MK_COMB (@lem75741) (@lem75740)). Qed.
Lemma lem75743 : term40 = term47.
Proof. exact (TRANS (@lem75735) (@lem75742)). Qed.
Lemma lem75745 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem75746 : term49 = term50.
Proof. exact (MK_COMB (@lem75745) (@lem75743)). Qed.
Lemma lem75747 : term29 = term49.
Proof. exact (@lem17160 ((NUMERAL 0) = (NUMERAL 0)) term36). Qed.
Lemma lem75756 : term29 = term50.
Proof. exact (TRANS (@lem75747) (@lem75746)). Qed.
Lemma lem75757 (h1 : term29) : term50.
Proof. exact (EQ_MP (@lem75756) (@lem75731 h1)). Qed.
Lemma lem75768 (n : nat) : (term44 n) = (term44 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem75769 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem75768 n)). Qed.
Lemma lem75770 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75771 : term47 = term47.
Proof. exact (MK_COMB (@lem75770) (@lem75769)). Qed.
Lemma lem75784 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem75785 : term50 = term50.
Proof. exact (MK_COMB (@lem75784) (@lem75771)). Qed.
Lemma lem75786 (h1 : term29) : term50.
Proof. exact (EQ_MP (@lem75785) (@lem75757 h1)). Qed.
Lemma lem75804 (h1 : term29) : term51.
Proof. exact (proj1 (@lem75786 h1)). Qed.
Lemma lem75826 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem75827 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem75826 (NUMERAL 0)). Qed.
Lemma lem75828 : term52.
Proof. exact (fun h0 : term51 => @lem75827). Qed.
Lemma lem75830 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem75831 : term52 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem75830 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem75832 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem75831) (@lem75828)). Qed.
Lemma lem75835 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem75837 : term51 = term54.
Proof. exact (@lem75835 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem75840 (h1 : term29) : term54.
Proof. exact (EQ_MP (@lem75837) (@lem75804 h1)). Qed.
Lemma lem75843 (h1 : term29) : False.
Proof. exact (@lem75840 h1 (@lem75832)). Qed.
Lemma lem75844 (h1 : term29) : term55.
Proof. exact (fun h0 : ~ False => @lem75843 h1). Qed.
Lemma lem75846 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem75847 : term55 = False.
Proof. exact (@lem75846 False). Qed.
Lemma lem75848 (h1 : term29) : False.
Proof. exact (EQ_MP (@lem75847) (@lem75844 h1)). Qed.
Lemma lem75849 (h1 : term29) : term29 = False.
Proof. exact (prop_ext (fun h2 : term29 => @lem75848 h1) (fun h2 : False => @lem75731 h1)). Qed.
Lemma lem75850 (h1 : term29) : False.
Proof. exact (EQ_MP (@lem75849 h1) (@lem75731 h1)). Qed.
Lemma lem75851 : term28.
Proof. exact (fun h0 : term29 => @lem75850 h0). Qed.
Lemma lem75852 : term4.
Proof. exact (EQ_MP (@lem75730) (@lem75851)). Qed.
Lemma lem75853 : term28.
Proof. exact (EQ_MP (@lem75726) (@lem75852)). Qed.
Lemma lem75855 : term28.
Proof. exact (@lem75689 (@lem75853)). Qed.
Lemma lem75856 (h1 : term29) : False.
Proof. exact (@lem75855 (@lem75674 h1)). Qed.
Lemma lem75857 (h1 : term29) : term29 = False.
Proof. exact (prop_ext (fun h2 : term29 => @lem75856 h1) (fun h2 : False => @lem75674 h1)). Qed.
Lemma lem75858 (h1 : term29) : False.
Proof. exact (EQ_MP (@lem75857 h1) (@lem75674 h1)). Qed.
Lemma lem75859 : term28.
Proof. exact (fun h0 : term29 => @lem75858 h0). Qed.
Lemma lem75860 : term4.
Proof. exact (EQ_MP (@lem75673) (@lem75859)). Qed.
Lemma lem75862 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem75863 (m : nat) : (term12 m) = (term56 m).
Proof. exact (@lem75862 (term12 m)). Qed.
Lemma lem75864 (m : nat) : (term56 m) = (term12 m).
Proof. exact (SYM (@lem75863 m)). Qed.
Lemma lem75865 (m : nat) (h1 : term57 m) : term57 m.
Proof. exact (h1). Qed.
Lemma lem75868 (m : nat) (h1 : term56 m) : term56 m.
Proof. exact (h1). Qed.
Lemma lem75869 (m : nat) : term58 m.
Proof. exact (fun h0 : term56 m => @lem75868 m h0). Qed.
Lemma lem75870 (m : nat) (h1 : term58 m) : term58 m.
Proof. exact (h1). Qed.
Lemma lem75871 (m : nat) (h1 : term56 m) : term56 m.
Proof. exact (h1). Qed.
Lemma lem75872 (m : nat) (h1 : term56 m) (h2 : term58 m) : term56 m.
Proof. exact (@lem75870 m h2 (@lem75871 m h1)). Qed.
Lemma lem75873 (m : nat) (h1 : term56 m) : term59 m.
Proof. exact (fun h0 : term58 m => @lem75872 m h1 h0). Qed.
Lemma lem75874 (m : nat) (h1 : term58 m) : term58 m.
Proof. exact (h1). Qed.
Lemma lem75875 (m : nat) (h1 : term56 m) (h2 : term58 m) : term56 m.
Proof. exact (@lem75873 m h1 (@lem75874 m h2)). Qed.
Lemma lem75876 (m : nat) (h1 : term58 m) : term58 m.
Proof. exact (fun h0 : term56 m => @lem75875 m h0 h1). Qed.
Lemma lem75877 (m : nat) : term60 m.
Proof. exact (fun h0 : term58 m => @lem75876 m h0). Qed.
Lemma lem75880 (m : nat) : term58 m.
Proof. exact (@lem75877 m (@lem75869 m)). Qed.
Lemma lem75886 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem75887 (m : nat) : (term56 m) = (term61 m).
Proof. exact (@lem75886 (term57 m)). Qed.
Lemma lem75889 (t : Prop) : (term34 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem75890 (m : nat) : (term61 m) = (term12 m).
Proof. exact (@lem75889 (term12 m)). Qed.
Lemma lem75893 (m : nat) : (term56 m) = (term12 m).
Proof. exact (TRANS (@lem75887 m) (@lem75890 m)). Qed.
Lemma lem75898 : term62 = term63.
Proof. exact (fun_ext (fun m : nat => @lem75893 m)). Qed.
Lemma lem75899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75952 : term64 = term65.
Proof. exact (MK_COMB (@lem75899) (@lem75898)). Qed.
Lemma lem75953 (m : nat) (n : nat) : ((S m) = (S n)) = ((S m) = (S n)).
Proof. exact (eq_refl ((S m) = (S n))). Qed.
Lemma lem75954 (m : nat) : (term66 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem75953 m n)). Qed.
Lemma lem75955 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem75956 (m : nat) : (term67 m) = (term67 m).
Proof. exact (MK_COMB (@lem75955) (@lem75954 m)). Qed.
Lemma lem75959 (m : nat) : (term68 m) = (term68 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem75960 (m : nat) : (term12 m) = (term12 m).
Proof. exact (MK_COMB (@lem75959 m) (@lem75956 m)). Qed.
Lemma lem75961 : term63 = term63.
Proof. exact (fun_ext (fun m : nat => @lem75960 m)). Qed.
Lemma lem75962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75963 : term65 = term65.
Proof. exact (MK_COMB (@lem75962) (@lem75961)). Qed.
Lemma lem75980 : term64 = term65.
Proof. exact (TRANS (@lem75952) (@lem75963)). Qed.
Lemma lem75981 : term65 = term64.
Proof. exact (SYM (@lem75980)). Qed.
Lemma lem75983 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem75984 (m : nat) : (term12 m) = (term56 m).
Proof. exact (@lem75983 (term12 m)). Qed.
Lemma lem75985 (m : nat) : (term56 m) = (term12 m).
Proof. exact (SYM (@lem75984 m)). Qed.
Lemma lem75986 (m : nat) (h1 : term57 m) : term57 m.
Proof. exact (h1). Qed.
Lemma lem75989 (P : nat -> Prop) : (term38 P) = (term39 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem75990 (m : nat) : (term69 m) = (term70 m).
Proof. exact (@lem75989 (term66 m)). Qed.
Lemma lem75991 (m : nat) (n : nat) : (term71 m n) = ((S m) = (S n)).
Proof. exact (eq_refl (term71 m n)). Qed.
Lemma lem75992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem75994 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem75992) (@lem75991 m n)). Qed.
Lemma lem75995 (m : nat) : (term74 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem75994 m n)). Qed.
Lemma lem75996 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75997 (m : nat) : (term70 m) = (term76 m).
Proof. exact (MK_COMB (@lem75996) (@lem75995 m)). Qed.
Lemma lem75998 (m : nat) : (term69 m) = (term76 m).
Proof. exact (TRANS (@lem75990 m) (@lem75997 m)). Qed.
Lemma lem76000 (m : nat) : (term77 m) = (term77 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem76001 (m : nat) : (term78 m) = (term79 m).
Proof. exact (MK_COMB (@lem76000 m) (@lem75998 m)). Qed.
Lemma lem76002 (m : nat) : (term57 m) = (term78 m).
Proof. exact (@lem17160 ((S m) = (NUMERAL 0)) (term67 m)). Qed.
Lemma lem76011 (m : nat) : (term57 m) = (term79 m).
Proof. exact (TRANS (@lem76002 m) (@lem76001 m)). Qed.
Lemma lem76012 (m : nat) (h1 : term57 m) : term79 m.
Proof. exact (EQ_MP (@lem76011 m) (@lem75986 m h1)). Qed.
Lemma lem76023 (m : nat) (n : nat) : (term73 m n) = (term73 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem76024 (m : nat) : (term75 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem76023 m n)). Qed.
Lemma lem76025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76026 (m : nat) : (term76 m) = (term76 m).
Proof. exact (MK_COMB (@lem76025) (@lem76024 m)). Qed.
Lemma lem76039 (m : nat) : (term77 m) = (term77 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem76040 (m : nat) : (term79 m) = (term79 m).
Proof. exact (MK_COMB (@lem76039 m) (@lem76026 m)). Qed.
Lemma lem76041 (m : nat) (h1 : term57 m) : term79 m.
Proof. exact (EQ_MP (@lem76040 m) (@lem76012 m h1)). Qed.
Lemma lem76042 (m : nat) (h1 : term57 m) : term76 m.
Proof. exact (proj2 (@lem76041 m h1)). Qed.
Lemma lem76049 (m : nat) (n : nat) : (term73 m n) = (term73 m n).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem76050 (m : nat) : (term75 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem76049 m n)). Qed.
Lemma lem76051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76053 (m : nat) : (term76 m) = (term76 m).
Proof. exact (MK_COMB (@lem76051) (@lem76050 m)). Qed.
Lemma lem76054 (m : nat) (h1 : term57 m) : term76 m.
Proof. exact (EQ_MP (@lem76053 m) (@lem76042 m h1)). Qed.
Lemma lem76055 (_2138 : nat) (m : nat) (h1 : term57 m) : term80 m _2138.
Proof. exact (@lem76054 m h1 _2138). Qed.
Lemma lem76056 (m : nat) (_2138 : nat) : (term80 m _2138) = (term73 m _2138).
Proof. exact (eq_refl (term80 m _2138)). Qed.
Lemma lem76061 (_2138 : nat) (m : nat) (h1 : term57 m) : term73 m _2138.
Proof. exact (EQ_MP (@lem76056 m _2138) (@lem76055 _2138 m h1)). Qed.
Lemma lem76081 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem76082 (m : nat) : (S m) = (S m).
Proof. exact (@lem76081 (S m)). Qed.
Lemma lem76083 (m : nat) : term81 m.
Proof. exact (fun h0 : term82 m => @lem76082 m). Qed.
Lemma lem76085 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem76086 (m : nat) : (term81 m) = ((S m) = (S m)).
Proof. exact (@lem76085 ((S m) = (S m))). Qed.
Lemma lem76087 (m : nat) : (S m) = (S m).
Proof. exact (EQ_MP (@lem76086 m) (@lem76083 m)). Qed.
Lemma lem76090 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem76092 (m : nat) (_2138 : nat) : (term73 m _2138) = (term83 m _2138).
Proof. exact (@lem76090 ((S m) = (S _2138))). Qed.
Lemma lem76095 (_2138 : nat) (m : nat) (h1 : term57 m) : term83 m _2138.
Proof. exact (EQ_MP (@lem76092 m _2138) (@lem76061 _2138 m h1)). Qed.
Lemma lem76096 (m : nat) (h1 : term57 m) : term84 m.
Proof. exact (@lem76095 m m h1). Qed.
Lemma lem76099 (m : nat) (h1 : term57 m) : False.
Proof. exact (@lem76096 m h1 (@lem76087 m)). Qed.
Lemma lem76100 (m : nat) (h1 : term57 m) : term55.
Proof. exact (fun h0 : ~ False => @lem76099 m h1). Qed.
Lemma lem76102 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem76103 : term55 = False.
Proof. exact (@lem76102 False). Qed.
Lemma lem76104 (m : nat) (h1 : term57 m) : False.
Proof. exact (EQ_MP (@lem76103) (@lem76100 m h1)). Qed.
Lemma lem76105 (m : nat) (h1 : term57 m) : (term57 m) = False.
Proof. exact (prop_ext (fun h2 : term57 m => @lem76104 m h1) (fun h2 : False => @lem75986 m h1)). Qed.
Lemma lem76106 (m : nat) (h1 : term57 m) : False.
Proof. exact (EQ_MP (@lem76105 m h1) (@lem75986 m h1)). Qed.
Lemma lem76107 (m : nat) : term56 m.
Proof. exact (fun h0 : term57 m => @lem76106 m h0). Qed.
Lemma lem76108 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem75985 m) (@lem76107 m)). Qed.
Lemma lem76113 : term65.
Proof. exact (fun m : nat => @lem76108 m). Qed.
Lemma lem76114 : term64.
Proof. exact (EQ_MP (@lem75981) (@lem76113)). Qed.
Lemma lem76115 (m : nat) : term85 m.
Proof. exact (@lem76114 m). Qed.
Lemma lem76116 (m : nat) : (term85 m) = (term56 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem76117 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem76116 m) (@lem76115 m)). Qed.
Lemma lem76119 (m : nat) : term56 m.
Proof. exact (@lem75880 m (@lem76117 m)). Qed.
Lemma lem76120 (m : nat) (h1 : term57 m) : False.
Proof. exact (@lem76119 m (@lem75865 m h1)). Qed.
Lemma lem76121 (m : nat) (h1 : term57 m) : (term57 m) = False.
Proof. exact (prop_ext (fun h2 : term57 m => @lem76120 m h1) (fun h2 : False => @lem75865 m h1)). Qed.
Lemma lem76122 (m : nat) (h1 : term57 m) : False.
Proof. exact (EQ_MP (@lem76121 m h1) (@lem75865 m h1)). Qed.
Lemma lem76123 (m : nat) : term56 m.
Proof. exact (fun h0 : term57 m => @lem76122 m h0). Qed.
Lemma lem76124 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem75864 m) (@lem76123 m)). Qed.
Lemma lem76125 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem76124 m). Qed.
Lemma lem76130 : term18.
Proof. exact (fun m : nat => @lem76125 m). Qed.
Lemma lem76131 : term20.
Proof. exact (conj (@lem75860) (@lem76130)). Qed.
Lemma lem76132 : term25.
Proof. exact (@lem75668 (@lem76131)). Qed.
