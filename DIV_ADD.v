Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIV_MULT_spec.
Require Import DIV_MULT_ADD_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3073436_spec.
Require Import thm3074596_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem3110729 (d : nat) : term0 d.
Proof. exact (@lem9784 (d = (NUMERAL 0))). Qed.
Lemma lem3110730 (d : nat) : (term0 d) = (term1 d).
Proof. exact (eq_refl (term0 d)). Qed.
Lemma lem3110731 (d : nat) : term1 d.
Proof. exact (EQ_MP (@lem3110730 d) (@lem3110729 d)). Qed.
Lemma lem3110733 (d : nat) (h1 : term2 d) : term2 d.
Proof. exact (h1). Qed.
Lemma lem3110754 : term3.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem3110755 (n : nat) : term4 n.
Proof. exact (@lem3110754 n). Qed.
Lemma lem3110756 (n : nat) : (term4 n) = ((term5 n) = n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem3110758 (n : nat) : term6 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem3110759 (n : nat) : (term6 n) = ((term7 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem3110764 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3110765 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem3110764 p q p' q'). Qed.
Lemma lem3110766 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem3110765 p q p'). Qed.
Lemma lem3110767 (a : nat) (b : nat) (d : nat) : term11 a b d.
Proof. exact (@lem3110766 (term12 a d b) ((term13 a b d) = (term14 a b d))). Qed.
Lemma lem3110768 (a : nat) (b : nat) (d : nat) (p' : Prop) : term15 a b d p'.
Proof. exact (@lem3110767 a b d p'). Qed.
Lemma lem3110769 (a : nat) (b : nat) (d : nat) (p' : Prop) : (term15 a b d p') = (term16 a b d p').
Proof. exact (eq_refl (term15 a b d p')). Qed.
Lemma lem3110770 (a : nat) (b : nat) (d : nat) (p' : Prop) : term16 a b d p'.
Proof. exact (EQ_MP (@lem3110769 a b d p') (@lem3110768 a b d p')). Qed.
Lemma lem3110771 (a : nat) (b : nat) (d : nat) (p' : Prop) (q' : Prop) : term17 a b d p' q'.
Proof. exact (@lem3110770 a b d p' q'). Qed.
Lemma lem3110772 (a : nat) (b : nat) (d : nat) (p' : Prop) (q' : Prop) : (term17 a b d p' q') = (term18 a b d p' q').
Proof. exact (eq_refl (term17 a b d p' q')). Qed.
Lemma lem3110773 (a : nat) (b : nat) (d : nat) (p' : Prop) (q' : Prop) : term18 a b d p' q'.
Proof. exact (EQ_MP (@lem3110772 a b d p' q') (@lem3110771 a b d p' q')). Qed.
Lemma lem3110777 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3110778 : num_divides = num_divides.
Proof. exact (eq_refl num_divides). Qed.
Lemma lem3110779 (d : nat) (h1 : d = (NUMERAL 0)) : (num_divides d) = term19.
Proof. exact (MK_COMB (@lem3110778) (@lem3110777 d h1)). Qed.
Lemma lem3110780 (a : nat) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3110781 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (num_divides d a) = (term20 a).
Proof. exact (MK_COMB (@lem3110779 d h1) (@lem3110780 a)). Qed.
Lemma lem3110782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3110783 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term21 d a) = (term22 a).
Proof. exact (MK_COMB (@lem3110782) (@lem3110781 a d h1)). Qed.
Lemma lem3110785 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3110786 : num_divides = num_divides.
Proof. exact (eq_refl num_divides). Qed.
Lemma lem3110787 (d : nat) (h1 : d = (NUMERAL 0)) : (num_divides d) = term19.
Proof. exact (MK_COMB (@lem3110786) (@lem3110785 d h1)). Qed.
Lemma lem3110788 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3110789 (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (num_divides d b) = (term20 b).
Proof. exact (MK_COMB (@lem3110787 d h1) (@lem3110788 b)). Qed.
Lemma lem3110790 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term12 a d b) = (term23 a b).
Proof. exact (MK_COMB (@lem3110783 a d h1) (@lem3110789 b d h1)). Qed.
Lemma lem3110793 (d : nat) (a : nat) (b : nat) (q' : Prop) : term24 d a b q'.
Proof. exact (@lem3110773 a b d (term23 a b) q'). Qed.
Lemma lem3110794 (a : nat) (b : nat) (q' : Prop) (d : nat) (h1 : d = (NUMERAL 0)) : term25 d a b q'.
Proof. exact (@lem3110793 d a b q' (@lem3110790 a b d h1)). Qed.
Lemma lem3110801 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3110802 (a : nat) (b : nat) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem3110803 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term13 a b d) = (term27 a b).
Proof. exact (MK_COMB (@lem3110802 a b) (@lem3110801 d h1)). Qed.
Lemma lem3110805 (n : nat) : (term7 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3110759 n) (@lem3110758 n)). Qed.
Lemma lem3110806 (a : nat) (b : nat) : (term27 a b) = (NUMERAL 0).
Proof. exact (@lem3110805 (Nat.add a b)). Qed.
Lemma lem3110807 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term13 a b d) = (NUMERAL 0).
Proof. exact (TRANS (@lem3110803 a b d h1) (@lem3110806 a b)). Qed.
Lemma lem3110808 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3110809 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term28 a b d) = term29.
Proof. exact (MK_COMB (@lem3110808) (@lem3110807 a b d h1)). Qed.
Lemma lem3110811 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3110812 (a : nat) : (Nat.div a) = (Nat.div a).
Proof. exact (eq_refl (Nat.div a)). Qed.
Lemma lem3110813 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.div a d) = (term7 a).
Proof. exact (MK_COMB (@lem3110812 a) (@lem3110811 d h1)). Qed.
Lemma lem3110815 (n : nat) : (term7 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3110759 n) (@lem3110758 n)). Qed.
Lemma lem3110816 (a : nat) : (term7 a) = (NUMERAL 0).
Proof. exact (@lem3110815 a). Qed.
Lemma lem3110817 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.div a d) = (NUMERAL 0).
Proof. exact (TRANS (@lem3110813 a d h1) (@lem3110816 a)). Qed.
Lemma lem3110818 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3110819 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term30 a d) = term31.
Proof. exact (MK_COMB (@lem3110818) (@lem3110817 a d h1)). Qed.
Lemma lem3110821 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3110822 (b : nat) : (Nat.div b) = (Nat.div b).
Proof. exact (eq_refl (Nat.div b)). Qed.
Lemma lem3110823 (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.div b d) = (term7 b).
Proof. exact (MK_COMB (@lem3110822 b) (@lem3110821 d h1)). Qed.
Lemma lem3110825 (n : nat) : (term7 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3110759 n) (@lem3110758 n)). Qed.
Lemma lem3110826 (b : nat) : (term7 b) = (NUMERAL 0).
Proof. exact (@lem3110825 b). Qed.
Lemma lem3110827 (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.div b d) = (NUMERAL 0).
Proof. exact (TRANS (@lem3110823 b d h1) (@lem3110826 b)). Qed.
Lemma lem3110828 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term14 a b d) = term32.
Proof. exact (MK_COMB (@lem3110819 a d h1) (@lem3110827 b d h1)). Qed.
Lemma lem3110830 (n : nat) : (term5 n) = n.
Proof. exact (EQ_MP (@lem3110756 n) (@lem3110755 n)). Qed.
Lemma lem3110831 : term32 = (NUMERAL 0).
Proof. exact (@lem3110830 (NUMERAL 0)). Qed.
Lemma lem3110832 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term14 a b d) = (NUMERAL 0).
Proof. exact (TRANS (@lem3110828 a b d h1) (@lem3110831)). Qed.
Lemma lem3110833 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : ((term13 a b d) = (term14 a b d)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3110809 a b d h1) (@lem3110832 a b d h1)). Qed.
Lemma lem3110835 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3110836 (x : nat) : (x = x) = True.
Proof. exact (@lem3110835 nat x). Qed.
Lemma lem3110837 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem3110836 (NUMERAL 0)). Qed.
Lemma lem3110838 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : ((term13 a b d) = (term14 a b d)) = True.
Proof. exact (TRANS (@lem3110833 a b d h1) (@lem3110837)). Qed.
Lemma lem3110839 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : term33 a b d.
Proof. exact (fun h0 : term23 a b => @lem3110838 a b d h1). Qed.
Lemma lem3110840 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : term34 d a b.
Proof. exact (@lem3110794 a b True d h1). Qed.
Lemma lem3110841 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term35 a b d) = (term36 a b).
Proof. exact (@lem3110840 a b d h1 (@lem3110839 a b d h1)). Qed.
Lemma lem3110843 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3110844 (a : nat) (b : nat) : (term36 a b) = True.
Proof. exact (@lem3110843 (term23 a b)). Qed.
Lemma lem3110845 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term35 a b d) = True.
Proof. exact (TRANS (@lem3110841 a b d h1) (@lem3110844 a b)). Qed.
Lemma lem3110846 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : True = (term35 a b d).
Proof. exact (SYM (@lem3110845 a b d h1)). Qed.
Lemma lem3110847 (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : term35 a b d.
Proof. exact (EQ_MP (@lem3110846 a b d h1) (@lem0)). Qed.
Lemma lem3110926 (b : nat) (a : nat) : (num_divides a b) = (term37 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
Lemma lem3110927 (a : nat) (d : nat) : (num_divides d a) = (term37 a d).
Proof. exact (@lem3110926 a d). Qed.
Lemma lem3110934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3110935 (a : nat) (d : nat) : (term21 d a) = (term38 a d).
Proof. exact (MK_COMB (@lem3110934) (@lem3110927 a d)). Qed.
Lemma lem3110937 (b : nat) (a : nat) : (num_divides a b) = (term37 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
Lemma lem3110938 (b : nat) (d : nat) : (num_divides d b) = (term37 b d).
Proof. exact (@lem3110937 b d). Qed.
Lemma lem3110945 (a : nat) (b : nat) (d : nat) : (term12 a d b) = (term39 a b d).
Proof. exact (MK_COMB (@lem3110935 a d) (@lem3110938 b d)). Qed.
Lemma lem3110948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3110949 (a : nat) (b : nat) (d : nat) : (term40 a d b) = (term41 a b d).
Proof. exact (MK_COMB (@lem3110948) (@lem3110945 a b d)). Qed.
Lemma lem3110952 (a : nat) (b : nat) (d : nat) : ((term13 a b d) = (term14 a b d)) = ((term13 a b d) = (term14 a b d)).
Proof. exact (eq_refl ((term13 a b d) = (term14 a b d))). Qed.
Lemma lem3110953 (a : nat) (b : nat) (d : nat) : (term35 a b d) = (term42 a b d).
Proof. exact (MK_COMB (@lem3110949 a b d) (@lem3110952 a b d)). Qed.
Lemma lem3110956 (a : nat) (b : nat) (d : nat) : (term42 a b d) = (term35 a b d).
Proof. exact (SYM (@lem3110953 a b d)). Qed.
Lemma lem3110957 (a : nat) (b : nat) (d : nat) (h1 : term39 a b d) : term39 a b d.
Proof. exact (h1). Qed.
Lemma lem3110958 (a : nat) (d : nat) (h1 : term37 a d) : term37 a d.
Proof. exact (h1). Qed.
Lemma lem3110959 (b : nat) (d : nat) (h1 : term37 b d) : term37 b d.
Proof. exact (h1). Qed.
Lemma lem3110960 (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : a = (Nat.mul d x).
Proof. exact (h1). Qed.
Lemma lem3110961 (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : b = (Nat.mul d x).
Proof. exact (h1). Qed.
Lemma lem3110962 (m : nat) : term43 m.
Proof. exact (@lem170527 m). Qed.
Lemma lem3110963 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem3110964 (m : nat) : term44 m.
Proof. exact (EQ_MP (@lem3110963 m) (@lem3110962 m)). Qed.
Lemma lem3110965 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem3110964 m n). Qed.
Lemma lem3110966 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem3110967 (m : nat) (n : nat) : term46 m n.
Proof. exact (EQ_MP (@lem3110966 m n) (@lem3110965 m n)). Qed.
Lemma lem3110968 (m : nat) (h1 : term2 m) : term2 m.
Proof. exact (h1). Qed.
Lemma lem3110969 (n : nat) (m : nat) (h1 : term2 m) : (term47 n m) = n.
Proof. exact (@lem3110967 m n (@lem3110968 m h1)). Qed.
Lemma lem3110975 : term48.
Proof. exact (proj2 (@lem209601)). Qed.
Lemma lem3111011 : term49.
Proof. exact (proj1 (@lem3110975)). Qed.
Lemma lem3111012 (a : nat) : term50 a.
Proof. exact (@lem3111011 a). Qed.
Lemma lem3111013 (a : nat) : (term50 a) = (term51 a).
Proof. exact (eq_refl (term50 a)). Qed.
Lemma lem3111014 (a : nat) : term51 a.
Proof. exact (EQ_MP (@lem3111013 a) (@lem3111012 a)). Qed.
Lemma lem3111015 (a : nat) (b : nat) : term52 a b.
Proof. exact (@lem3111014 a b). Qed.
Lemma lem3111016 (a : nat) (b : nat) : (term52 a b) = (term53 a b).
Proof. exact (eq_refl (term52 a b)). Qed.
Lemma lem3111017 (a : nat) (b : nat) : term53 a b.
Proof. exact (EQ_MP (@lem3111016 a b) (@lem3111015 a b)). Qed.
Lemma lem3111018 (a : nat) (b : nat) (n : nat) : term54 a b n.
Proof. exact (@lem3111017 a b n). Qed.
Lemma lem3111019 (a : nat) (b : nat) (n : nat) : (term54 a b n) = (term55 a b n).
Proof. exact (eq_refl (term54 a b n)). Qed.
Lemma lem3111020 (a : nat) (b : nat) (n : nat) : term55 a b n.
Proof. exact (EQ_MP (@lem3111019 a b n) (@lem3111018 a b n)). Qed.
Lemma lem3111021 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (h1). Qed.
Lemma lem3111022 (a : nat) (b : nat) (n : nat) (h1 : term2 n) : (term56 a b n) = (term57 a b n).
Proof. exact (@lem3111020 a b n (@lem3111021 n h1)). Qed.
Lemma lem3111045 (d : nat) : term58 d.
Proof. exact (@lem82 (d = (NUMERAL 0))). Qed.
Lemma lem3111061 (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : a = (Nat.mul d x).
Proof. exact (h1). Qed.
Lemma lem3111062 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3111063 (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : (Nat.add a) = (term59 d x).
Proof. exact (MK_COMB (@lem3111062) (@lem3111061 a d x h1)). Qed.
Lemma lem3111064 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3111065 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : (Nat.add a b) = (term60 d x b).
Proof. exact (MK_COMB (@lem3111063 a d x h1) (@lem3111064 b)). Qed.
Lemma lem3111066 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem3111067 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : (term26 a b) = (term61 d x b).
Proof. exact (MK_COMB (@lem3111066) (@lem3111065 b a d x h1)). Qed.
Lemma lem3111068 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem3111069 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : (term13 a b d) = (term56 x b d).
Proof. exact (MK_COMB (@lem3111067 b a d x h1) (@lem3111068 d)). Qed.
Lemma lem3111071 (a : nat) (b : nat) (n : nat) : term55 a b n.
Proof. exact (fun h0 : term2 n => @lem3111022 a b n h0). Qed.
Lemma lem3111072 (x : nat) (b : nat) (d : nat) : term55 x b d.
Proof. exact (@lem3111071 x b d). Qed.
Lemma lem3111074 (d : nat) (h1 : term2 d) : (d = (NUMERAL 0)) = False.
Proof. exact (@lem3111045 d (@lem3110733 d h1)). Qed.
Lemma lem3111075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3111076 (d : nat) (h1 : term2 d) : (term2 d) = (~ False).
Proof. exact (MK_COMB (@lem3111075) (@lem3111074 d h1)). Qed.
Lemma lem3111078 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3111079 (d : nat) (h1 : term2 d) : (term2 d) = True.
Proof. exact (TRANS (@lem3111076 d h1) (@lem3111078)). Qed.
Lemma lem3111080 (d : nat) (h1 : term2 d) : True = (term2 d).
Proof. exact (SYM (@lem3111079 d h1)). Qed.
Lemma lem3111081 (d : nat) (h1 : term2 d) : term2 d.
Proof. exact (EQ_MP (@lem3111080 d h1) (@lem0)). Qed.
Lemma lem3111082 (x : nat) (b : nat) (d : nat) (h1 : term2 d) : (term56 x b d) = (term57 x b d).
Proof. exact (@lem3111072 x b d (@lem3111081 d h1)). Qed.
Lemma lem3111083 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (term13 a b d) = (term57 x b d).
Proof. exact (TRANS (@lem3111069 b a d x h2) (@lem3111082 x b d h1)). Qed.
Lemma lem3111084 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3111085 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (term28 a b d) = (term62 x b d).
Proof. exact (MK_COMB (@lem3111084) (@lem3111083 b a d x h1 h2)). Qed.
Lemma lem3111087 (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : a = (Nat.mul d x).
Proof. exact (h1). Qed.
Lemma lem3111088 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem3111089 (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : (Nat.div a) = (term63 d x).
Proof. exact (MK_COMB (@lem3111088) (@lem3111087 a d x h1)). Qed.
Lemma lem3111090 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem3111091 (a : nat) (d : nat) (x : nat) (h1 : a = (Nat.mul d x)) : (Nat.div a d) = (term47 x d).
Proof. exact (MK_COMB (@lem3111089 a d x h1) (@lem3111090 d)). Qed.
Lemma lem3111093 (m : nat) (n : nat) : term46 m n.
Proof. exact (fun h0 : term2 m => @lem3110969 n m h0). Qed.
Lemma lem3111094 (d : nat) (x : nat) : term46 d x.
Proof. exact (@lem3111093 d x). Qed.
Lemma lem3111096 (d : nat) (h1 : term2 d) : (d = (NUMERAL 0)) = False.
Proof. exact (@lem3111045 d (@lem3110733 d h1)). Qed.
Lemma lem3111097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3111098 (d : nat) (h1 : term2 d) : (term2 d) = (~ False).
Proof. exact (MK_COMB (@lem3111097) (@lem3111096 d h1)). Qed.
Lemma lem3111100 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3111101 (d : nat) (h1 : term2 d) : (term2 d) = True.
Proof. exact (TRANS (@lem3111098 d h1) (@lem3111100)). Qed.
Lemma lem3111102 (d : nat) (h1 : term2 d) : True = (term2 d).
Proof. exact (SYM (@lem3111101 d h1)). Qed.
Lemma lem3111103 (d : nat) (h1 : term2 d) : term2 d.
Proof. exact (EQ_MP (@lem3111102 d h1) (@lem0)). Qed.
Lemma lem3111104 (x : nat) (d : nat) (h1 : term2 d) : (term47 x d) = x.
Proof. exact (@lem3111094 d x (@lem3111103 d h1)). Qed.
Lemma lem3111105 (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (Nat.div a d) = x.
Proof. exact (TRANS (@lem3111091 a d x h2) (@lem3111104 x d h1)). Qed.
Lemma lem3111106 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3111107 (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (term30 a d) = (Nat.add x).
Proof. exact (MK_COMB (@lem3111106) (@lem3111105 a d x h1 h2)). Qed.
Lemma lem3111108 (b : nat) (d : nat) : (Nat.div b d) = (Nat.div b d).
Proof. exact (eq_refl (Nat.div b d)). Qed.
Lemma lem3111109 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (term14 a b d) = (term57 x b d).
Proof. exact (MK_COMB (@lem3111107 a d x h1 h2) (@lem3111108 b d)). Qed.
Lemma lem3111110 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : ((term13 a b d) = (term14 a b d)) = ((term57 x b d) = (term57 x b d)).
Proof. exact (MK_COMB (@lem3111085 b a d x h1 h2) (@lem3111109 b a d x h1 h2)). Qed.
Lemma lem3111112 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3111113 (x : nat) : (x = x) = True.
Proof. exact (@lem3111112 nat x). Qed.
Lemma lem3111114 (x : nat) (b : nat) (d : nat) : ((term57 x b d) = (term57 x b d)) = True.
Proof. exact (@lem3111113 (term57 x b d)). Qed.
Lemma lem3111115 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : ((term13 a b d) = (term14 a b d)) = True.
Proof. exact (TRANS (@lem3111110 b a d x h1 h2) (@lem3111114 x b d)). Qed.
Lemma lem3111116 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : True = ((term13 a b d) = (term14 a b d)).
Proof. exact (SYM (@lem3111115 b a d x h1 h2)). Qed.
Lemma lem3111117 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (term13 a b d) = (term14 a b d).
Proof. exact (EQ_MP (@lem3111116 b a d x h1 h2) (@lem0)). Qed.
Lemma lem3111118 (m : nat) : term43 m.
Proof. exact (@lem170527 m). Qed.
Lemma lem3111119 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem3111120 (m : nat) : term44 m.
Proof. exact (EQ_MP (@lem3111119 m) (@lem3111118 m)). Qed.
Lemma lem3111121 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem3111120 m n). Qed.
Lemma lem3111122 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem3111123 (m : nat) (n : nat) : term46 m n.
Proof. exact (EQ_MP (@lem3111122 m n) (@lem3111121 m n)). Qed.
Lemma lem3111124 (m : nat) (h1 : term2 m) : term2 m.
Proof. exact (h1). Qed.
Lemma lem3111125 (n : nat) (m : nat) (h1 : term2 m) : (term47 n m) = n.
Proof. exact (@lem3111123 m n (@lem3111124 m h1)). Qed.
Lemma lem3111131 : term48.
Proof. exact (proj2 (@lem209601)). Qed.
Lemma lem3111132 : term64.
Proof. exact (proj2 (@lem3111131)). Qed.
Lemma lem3111133 : term65.
Proof. exact (proj2 (@lem3111132)). Qed.
Lemma lem3111134 (a : nat) : term66 a.
Proof. exact (@lem3111133 a). Qed.
Lemma lem3111135 (a : nat) : (term66 a) = (term67 a).
Proof. exact (eq_refl (term66 a)). Qed.
Lemma lem3111136 (a : nat) : term67 a.
Proof. exact (EQ_MP (@lem3111135 a) (@lem3111134 a)). Qed.
Lemma lem3111137 (a : nat) (b : nat) : term68 a b.
Proof. exact (@lem3111136 a b). Qed.
Lemma lem3111138 (b : nat) (a : nat) : (term68 a b) = (term69 b a).
Proof. exact (eq_refl (term68 a b)). Qed.
Lemma lem3111139 (b : nat) (a : nat) : term69 b a.
Proof. exact (EQ_MP (@lem3111138 b a) (@lem3111137 a b)). Qed.
Lemma lem3111140 (b : nat) (a : nat) (n : nat) : term70 b a n.
Proof. exact (@lem3111139 b a n). Qed.
Lemma lem3111141 (b : nat) (n : nat) (a : nat) : (term70 b a n) = (term71 b n a).
Proof. exact (eq_refl (term70 b a n)). Qed.
Lemma lem3111142 (b : nat) (n : nat) (a : nat) : term71 b n a.
Proof. exact (EQ_MP (@lem3111141 b n a) (@lem3111140 b a n)). Qed.
Lemma lem3111143 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (h1). Qed.
Lemma lem3111144 (b : nat) (a : nat) (n : nat) (h1 : term2 n) : (term72 b a n) = (term73 b n a).
Proof. exact (@lem3111142 b n a (@lem3111143 n h1)). Qed.
Lemma lem3111201 (d : nat) : term58 d.
Proof. exact (@lem82 (d = (NUMERAL 0))). Qed.
Lemma lem3111217 (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : b = (Nat.mul d x).
Proof. exact (h1). Qed.
Lemma lem3111218 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem3111219 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : (Nat.add a b) = (term74 a d x).
Proof. exact (MK_COMB (@lem3111218 a) (@lem3111217 b d x h1)). Qed.
Lemma lem3111220 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem3111221 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : (term26 a b) = (term75 a d x).
Proof. exact (MK_COMB (@lem3111220) (@lem3111219 a b d x h1)). Qed.
Lemma lem3111222 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem3111223 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : (term13 a b d) = (term72 a x d).
Proof. exact (MK_COMB (@lem3111221 a b d x h1) (@lem3111222 d)). Qed.
Lemma lem3111225 (b : nat) (n : nat) (a : nat) : term71 b n a.
Proof. exact (fun h0 : term2 n => @lem3111144 b a n h0). Qed.
Lemma lem3111226 (a : nat) (d : nat) (x : nat) : term71 a d x.
Proof. exact (@lem3111225 a d x). Qed.
Lemma lem3111228 (d : nat) (h1 : term2 d) : (d = (NUMERAL 0)) = False.
Proof. exact (@lem3111201 d (@lem3110733 d h1)). Qed.
Lemma lem3111229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3111230 (d : nat) (h1 : term2 d) : (term2 d) = (~ False).
Proof. exact (MK_COMB (@lem3111229) (@lem3111228 d h1)). Qed.
Lemma lem3111232 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3111233 (d : nat) (h1 : term2 d) : (term2 d) = True.
Proof. exact (TRANS (@lem3111230 d h1) (@lem3111232)). Qed.
Lemma lem3111234 (d : nat) (h1 : term2 d) : True = (term2 d).
Proof. exact (SYM (@lem3111233 d h1)). Qed.
Lemma lem3111235 (d : nat) (h1 : term2 d) : term2 d.
Proof. exact (EQ_MP (@lem3111234 d h1) (@lem0)). Qed.
Lemma lem3111236 (a : nat) (x : nat) (d : nat) (h1 : term2 d) : (term72 a x d) = (term73 a d x).
Proof. exact (@lem3111226 a d x (@lem3111235 d h1)). Qed.
Lemma lem3111237 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (term13 a b d) = (term73 a d x).
Proof. exact (TRANS (@lem3111223 a b d x h2) (@lem3111236 a x d h1)). Qed.
Lemma lem3111238 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3111239 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (term28 a b d) = (term76 a d x).
Proof. exact (MK_COMB (@lem3111238) (@lem3111237 a b d x h1 h2)). Qed.
Lemma lem3111241 (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : b = (Nat.mul d x).
Proof. exact (h1). Qed.
Lemma lem3111242 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem3111243 (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : (Nat.div b) = (term63 d x).
Proof. exact (MK_COMB (@lem3111242) (@lem3111241 b d x h1)). Qed.
Lemma lem3111244 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem3111245 (b : nat) (d : nat) (x : nat) (h1 : b = (Nat.mul d x)) : (Nat.div b d) = (term47 x d).
Proof. exact (MK_COMB (@lem3111243 b d x h1) (@lem3111244 d)). Qed.
Lemma lem3111247 (m : nat) (n : nat) : term46 m n.
Proof. exact (fun h0 : term2 m => @lem3111125 n m h0). Qed.
Lemma lem3111248 (d : nat) (x : nat) : term46 d x.
Proof. exact (@lem3111247 d x). Qed.
Lemma lem3111250 (d : nat) (h1 : term2 d) : (d = (NUMERAL 0)) = False.
Proof. exact (@lem3111201 d (@lem3110733 d h1)). Qed.
Lemma lem3111251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3111252 (d : nat) (h1 : term2 d) : (term2 d) = (~ False).
Proof. exact (MK_COMB (@lem3111251) (@lem3111250 d h1)). Qed.
Lemma lem3111254 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3111255 (d : nat) (h1 : term2 d) : (term2 d) = True.
Proof. exact (TRANS (@lem3111252 d h1) (@lem3111254)). Qed.
Lemma lem3111256 (d : nat) (h1 : term2 d) : True = (term2 d).
Proof. exact (SYM (@lem3111255 d h1)). Qed.
Lemma lem3111257 (d : nat) (h1 : term2 d) : term2 d.
Proof. exact (EQ_MP (@lem3111256 d h1) (@lem0)). Qed.
Lemma lem3111258 (x : nat) (d : nat) (h1 : term2 d) : (term47 x d) = x.
Proof. exact (@lem3111248 d x (@lem3111257 d h1)). Qed.
Lemma lem3111259 (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (Nat.div b d) = x.
Proof. exact (TRANS (@lem3111245 b d x h2) (@lem3111258 x d h1)). Qed.
Lemma lem3111260 (a : nat) (d : nat) : (term30 a d) = (term30 a d).
Proof. exact (eq_refl (term30 a d)). Qed.
Lemma lem3111261 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (term14 a b d) = (term73 a d x).
Proof. exact (MK_COMB (@lem3111260 a d) (@lem3111259 b d x h1 h2)). Qed.
Lemma lem3111262 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : ((term13 a b d) = (term14 a b d)) = ((term73 a d x) = (term73 a d x)).
Proof. exact (MK_COMB (@lem3111239 a b d x h1 h2) (@lem3111261 a b d x h1 h2)). Qed.
Lemma lem3111264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3111265 (x : nat) : (x = x) = True.
Proof. exact (@lem3111264 nat x). Qed.
Lemma lem3111266 (a : nat) (d : nat) (x : nat) : ((term73 a d x) = (term73 a d x)) = True.
Proof. exact (@lem3111265 (term73 a d x)). Qed.
Lemma lem3111267 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : ((term13 a b d) = (term14 a b d)) = True.
Proof. exact (TRANS (@lem3111262 a b d x h1 h2) (@lem3111266 a d x)). Qed.
Lemma lem3111268 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : True = ((term13 a b d) = (term14 a b d)).
Proof. exact (SYM (@lem3111267 a b d x h1 h2)). Qed.
Lemma lem3111269 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (term13 a b d) = (term14 a b d).
Proof. exact (EQ_MP (@lem3111268 a b d x h1 h2) (@lem0)). Qed.
Lemma lem3111270 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (b = (Nat.mul d x)) = ((term13 a b d) = (term14 a b d)).
Proof. exact (prop_ext (fun h3 : b = (Nat.mul d x) => @lem3111269 a b d x h1 h2) (fun h3 : (term13 a b d) = (term14 a b d) => @lem3110961 b d x h2)). Qed.
Lemma lem3111271 (a : nat) (b : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : b = (Nat.mul d x)) : (term13 a b d) = (term14 a b d).
Proof. exact (EQ_MP (@lem3111270 a b d x h1 h2) (@lem3110961 b d x h2)). Qed.
Lemma lem3111272 (a : nat) (b : nat) (d : nat) (h1 : term37 b d) (h2 : term2 d) : (term13 a b d) = (term14 a b d).
Proof. exact (ex_elim (@lem3110959 b d h1) (fun x : nat => fun h0 : term77 b d x => @lem3111271 a b d x h2 h0)). Qed.
Lemma lem3111273 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (a = (Nat.mul d x)) = ((term13 a b d) = (term14 a b d)).
Proof. exact (prop_ext (fun h3 : a = (Nat.mul d x) => @lem3111117 b a d x h1 h2) (fun h3 : (term13 a b d) = (term14 a b d) => @lem3110960 a d x h2)). Qed.
Lemma lem3111274 (b : nat) (a : nat) (d : nat) (x : nat) (h1 : term2 d) (h2 : a = (Nat.mul d x)) : (term13 a b d) = (term14 a b d).
Proof. exact (EQ_MP (@lem3111273 b a d x h1 h2) (@lem3110960 a d x h2)). Qed.
Lemma lem3111275 (b : nat) (a : nat) (d : nat) (h1 : term37 a d) (h2 : term2 d) : (term13 a b d) = (term14 a b d).
Proof. exact (ex_elim (@lem3110958 a d h1) (fun x : nat => fun h0 : term77 a d x => @lem3111274 b a d x h2 h0)). Qed.
Lemma lem3111276 (a : nat) (b : nat) (d : nat) (h1 : term2 d) (h2 : term39 a b d) : (term13 a b d) = (term14 a b d).
Proof. exact (or_elim (@lem3110957 a b d h2) (fun h0 : term37 a d => @lem3111275 b a d h0 h1) (fun h0 : term37 b d => @lem3111272 a b d h0 h1)). Qed.
Lemma lem3111277 (a : nat) (b : nat) (d : nat) (h1 : term2 d) : term42 a b d.
Proof. exact (fun h0 : term39 a b d => @lem3111276 a b d h1 h0). Qed.
Lemma lem3111279 (a : nat) (b : nat) (d : nat) (h1 : term2 d) : term35 a b d.
Proof. exact (EQ_MP (@lem3110956 a b d) (@lem3111277 a b d h1)). Qed.
Lemma lem3111280 (a : nat) (b : nat) (d : nat) : term35 a b d.
Proof. exact (or_elim (@lem3110731 d) (fun h0 : d = (NUMERAL 0) => @lem3110847 a b d h0) (fun h0 : term2 d => @lem3111279 a b d h0)). Qed.
Lemma lem3111285 (a : nat) (d : nat) : term78 a d.
Proof. exact (fun b : nat => @lem3111280 a b d). Qed.
Lemma lem3111290 (d : nat) : term79 d.
Proof. exact (fun a : nat => @lem3111285 a d). Qed.
Lemma lem3111295 : term80.
Proof. exact (fun d : nat => @lem3111290 d). Qed.
