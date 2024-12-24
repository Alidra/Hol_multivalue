Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CART_EQ_FULL_term_abbrevs.
Require Import CART_EQ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Lemma lem7629769 {A B : Type'} (x : cart A B) : term0 A B x.
Proof. exact (@lem7617066 A B x). Qed.
Lemma lem7629770 {A B : Type'} (x : cart A B) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem7629771 {A B : Type'} (x : cart A B) : term1 A B x.
Proof. exact (EQ_MP (@lem7629770 A B x) (@lem7629769 A B x)). Qed.
Lemma lem7629772 {A B : Type'} (x : cart A B) (y : cart A B) : term2 A B x y.
Proof. exact (@lem7629771 A B x y). Qed.
Lemma lem7629773 {A B : Type'} (x : cart A B) (y : cart A B) : (term2 A B x y) = ((x = y) = (term3 A B x y)).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem7629780 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term4 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7629781 (p : Prop) (q : Prop) (p' : Prop) : term5 p q p'.
Proof. exact (fun q' : Prop => @lem7629780 p q p' q'). Qed.
Lemma lem7629782 (p : Prop) (q : Prop) : term6 p q.
Proof. exact (fun p' : Prop => @lem7629781 p q p'). Qed.
Lemma lem7629783 {A N : Type'} (x : cart A N) (y : cart A N) : term7 A N x y.
Proof. exact (@lem7629782 (x = y) (term8 A N x y)). Qed.
Lemma lem7629784 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) : term9 A N x y p'.
Proof. exact (@lem7629783 A N x y p'). Qed.
Lemma lem7629785 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) : (term9 A N x y p') = (term10 A N x y p').
Proof. exact (eq_refl (term9 A N x y p')). Qed.
Lemma lem7629786 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) : term10 A N x y p'.
Proof. exact (EQ_MP (@lem7629785 A N x y p') (@lem7629784 A N x y p')). Qed.
Lemma lem7629787 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) (q' : Prop) : term11 A N x y p' q'.
Proof. exact (@lem7629786 A N x y p' q'). Qed.
Lemma lem7629788 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) (q' : Prop) : (term11 A N x y p' q') = (term12 A N x y p' q').
Proof. exact (eq_refl (term11 A N x y p' q')). Qed.
Lemma lem7629789 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) (q' : Prop) : term12 A N x y p' q'.
Proof. exact (EQ_MP (@lem7629788 A N x y p' q') (@lem7629787 A N x y p' q')). Qed.
Lemma lem7629792 {A N : Type'} (x : cart A N) (y : cart A N) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7629793 {A N : Type'} (x : cart A N) (y : cart A N) (q' : Prop) : term13 A N x y q'.
Proof. exact (@lem7629789 A N x y (x = y) q'). Qed.
Lemma lem7629794 {A N : Type'} (x : cart A N) (y : cart A N) (q' : Prop) : term14 A N x y q'.
Proof. exact (@lem7629793 A N x y q' (@lem7629792 A N x y)). Qed.
Lemma lem7629803 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem7629804 {A N : Type'} : (@dollar A N) = (@dollar A N).
Proof. exact (eq_refl (@dollar A N)). Qed.
Lemma lem7629805 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : x = y) : (@dollar A N x) = (@dollar A N y).
Proof. exact (MK_COMB (@lem7629804 A N) (@lem7629803 A N x y h1)). Qed.
Lemma lem7629806 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7629807 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : x = y) : (@dollar A N x i) = (@dollar A N y i).
Proof. exact (MK_COMB (@lem7629805 A N x y h1) (@lem7629806 i)). Qed.
Lemma lem7629808 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7629809 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : x = y) : (term15 A N x i) = (term15 A N y i).
Proof. exact (MK_COMB (@lem7629808 A) (@lem7629807 A N i x y h1)). Qed.
Lemma lem7629810 {A N : Type'} (y : cart A N) (i : nat) : (@dollar A N y i) = (@dollar A N y i).
Proof. exact (eq_refl (@dollar A N y i)). Qed.
Lemma lem7629811 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : x = y) : ((@dollar A N x i) = (@dollar A N y i)) = ((@dollar A N y i) = (@dollar A N y i)).
Proof. exact (MK_COMB (@lem7629809 A N i x y h1) (@lem7629810 A N y i)). Qed.
Lemma lem7629813 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7629814 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7629813 A x). Qed.
Lemma lem7629815 {A N : Type'} (y : cart A N) (i : nat) : ((@dollar A N y i) = (@dollar A N y i)) = True.
Proof. exact (@lem7629814 A (@dollar A N y i)). Qed.
Lemma lem7629816 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : x = y) : ((@dollar A N x i) = (@dollar A N y i)) = True.
Proof. exact (TRANS (@lem7629811 A N i x y h1) (@lem7629815 A N y i)). Qed.
Lemma lem7629817 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : x = y) : (term16 A N x y) = term17.
Proof. exact (fun_ext (fun i : nat => @lem7629816 A N i x y h1)). Qed.
Lemma lem7629818 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7629819 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : x = y) : (term8 A N x y) = term18.
Proof. exact (MK_COMB (@lem7629818) (@lem7629817 A N x y h1)). Qed.
Lemma lem7629821 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7629822 (t : Prop) : (term20 t) = t.
Proof. exact (@lem7629821 nat t). Qed.
Lemma lem7629823 : term18 = True.
Proof. exact (@lem7629822 True). Qed.
Lemma lem7629824 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : x = y) : (term8 A N x y) = True.
Proof. exact (TRANS (@lem7629819 A N x y h1) (@lem7629823)). Qed.
Lemma lem7629825 {A N : Type'} (x : cart A N) (y : cart A N) : term21 A N x y.
Proof. exact (fun h0 : x = y => @lem7629824 A N x y h0). Qed.
Lemma lem7629826 {A N : Type'} (x : cart A N) (y : cart A N) : term22 A N x y.
Proof. exact (@lem7629794 A N x y True). Qed.
Lemma lem7629827 {A N : Type'} (x : cart A N) (y : cart A N) : (term23 A N x y) = (term24 A N x y).
Proof. exact (@lem7629826 A N x y (@lem7629825 A N x y)). Qed.
Lemma lem7629831 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7629832 {A N : Type'} (x : cart A N) (y : cart A N) : (term24 A N x y) = True.
Proof. exact (@lem7629831 (x = y)). Qed.
Lemma lem7629833 {A N : Type'} (x : cart A N) (y : cart A N) : (term23 A N x y) = True.
Proof. exact (TRANS (@lem7629827 A N x y) (@lem7629832 A N x y)). Qed.
Lemma lem7629834 {A N : Type'} (x : cart A N) (y : cart A N) : True = (term23 A N x y).
Proof. exact (SYM (@lem7629833 A N x y)). Qed.
Lemma lem7629835 {A N : Type'} (x : cart A N) (y : cart A N) : term23 A N x y.
Proof. exact (EQ_MP (@lem7629834 A N x y) (@lem0)). Qed.
Lemma lem7629881 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term4 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7629882 (p : Prop) (q : Prop) (p' : Prop) : term5 p q p'.
Proof. exact (fun q' : Prop => @lem7629881 p q p' q'). Qed.
Lemma lem7629883 (p : Prop) (q : Prop) : term6 p q.
Proof. exact (fun p' : Prop => @lem7629882 p q p'). Qed.
Lemma lem7629884 {A N : Type'} (x : cart A N) (y : cart A N) : term25 A N x y.
Proof. exact (@lem7629883 (term8 A N x y) (x = y)). Qed.
Lemma lem7629885 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) : term26 A N x y p'.
Proof. exact (@lem7629884 A N x y p'). Qed.
Lemma lem7629886 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) : (term26 A N x y p') = (term27 A N x y p').
Proof. exact (eq_refl (term26 A N x y p')). Qed.
Lemma lem7629887 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) : term27 A N x y p'.
Proof. exact (EQ_MP (@lem7629886 A N x y p') (@lem7629885 A N x y p')). Qed.
Lemma lem7629888 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) (q' : Prop) : term28 A N x y p' q'.
Proof. exact (@lem7629887 A N x y p' q'). Qed.
Lemma lem7629889 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) (q' : Prop) : (term28 A N x y p' q') = (term29 A N x y p' q').
Proof. exact (eq_refl (term28 A N x y p' q')). Qed.
Lemma lem7629890 {A N : Type'} (x : cart A N) (y : cart A N) (p' : Prop) (q' : Prop) : term29 A N x y p' q'.
Proof. exact (EQ_MP (@lem7629889 A N x y p' q') (@lem7629888 A N x y p' q')). Qed.
Lemma lem7629899 {A N : Type'} (x : cart A N) (y : cart A N) : (term8 A N x y) = (term8 A N x y).
Proof. exact (eq_refl (term8 A N x y)). Qed.
Lemma lem7629900 {A N : Type'} (x : cart A N) (y : cart A N) (q' : Prop) : term30 A N x y q'.
Proof. exact (@lem7629890 A N x y (term8 A N x y) q'). Qed.
Lemma lem7629901 {A N : Type'} (x : cart A N) (y : cart A N) (q' : Prop) : term31 A N x y q'.
Proof. exact (@lem7629900 A N x y q' (@lem7629899 A N x y)). Qed.
Lemma lem7629902 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : term8 A N x y.
Proof. exact (h1). Qed.
Lemma lem7629903 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : term32 A N x y i.
Proof. exact (@lem7629902 A N x y h1 i). Qed.
Lemma lem7629904 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) : (term32 A N x y i) = ((@dollar A N x i) = (@dollar A N y i)).
Proof. exact (eq_refl (term32 A N x y i)). Qed.
Lemma lem7629909 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term3 A B x y).
Proof. exact (EQ_MP (@lem7629773 A B x y) (@lem7629772 A B x y)). Qed.
Lemma lem7629910 {A N : Type'} (x : cart A N) (y : cart A N) : (x = y) = (term3 A N x y).
Proof. exact (@lem7629909 A N x y). Qed.
Lemma lem7629918 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term4 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7629919 (p : Prop) (q : Prop) (p' : Prop) : term5 p q p'.
Proof. exact (fun q' : Prop => @lem7629918 p q p' q'). Qed.
Lemma lem7629920 (p : Prop) (q : Prop) : term6 p q.
Proof. exact (fun p' : Prop => @lem7629919 p q p'). Qed.
Lemma lem7629921 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) : term33 A N x y i.
Proof. exact (@lem7629920 (term34 N i) ((@dollar A N x i) = (@dollar A N y i))). Qed.
Lemma lem7629922 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (p' : Prop) : term35 A N x y i p'.
Proof. exact (@lem7629921 A N x y i p'). Qed.
Lemma lem7629923 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (p' : Prop) : (term35 A N x y i p') = (term36 A N x y i p').
Proof. exact (eq_refl (term35 A N x y i p')). Qed.
Lemma lem7629924 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (p' : Prop) : term36 A N x y i p'.
Proof. exact (EQ_MP (@lem7629923 A N x y i p') (@lem7629922 A N x y i p')). Qed.
Lemma lem7629925 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (p' : Prop) (q' : Prop) : term37 A N x y i p' q'.
Proof. exact (@lem7629924 A N x y i p' q'). Qed.
Lemma lem7629926 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (p' : Prop) (q' : Prop) : (term37 A N x y i p' q') = (term38 A N x y i p' q').
Proof. exact (eq_refl (term37 A N x y i p' q')). Qed.
Lemma lem7629927 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (p' : Prop) (q' : Prop) : term38 A N x y i p' q'.
Proof. exact (EQ_MP (@lem7629926 A N x y i p' q') (@lem7629925 A N x y i p' q')). Qed.
Lemma lem7629930 {N : Type'} (i : nat) : (term34 N i) = (term34 N i).
Proof. exact (eq_refl (term34 N i)). Qed.
Lemma lem7629931 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (q' : Prop) : term39 A N x y i q'.
Proof. exact (@lem7629927 A N x y i (term34 N i) q'). Qed.
Lemma lem7629932 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) (q' : Prop) : term40 A N x y i q'.
Proof. exact (@lem7629931 A N x y i q' (@lem7629930 N i)). Qed.
Lemma lem7629945 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (@dollar A N x i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7629904 A N x y i) (@lem7629903 A N i x y h1)). Qed.
Lemma lem7629946 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7629947 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (term15 A N x i) = (term15 A N y i).
Proof. exact (MK_COMB (@lem7629946 A) (@lem7629945 A N i x y h1)). Qed.
Lemma lem7629948 {A N : Type'} (y : cart A N) (i : nat) : (@dollar A N y i) = (@dollar A N y i).
Proof. exact (eq_refl (@dollar A N y i)). Qed.
Lemma lem7629949 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : ((@dollar A N x i) = (@dollar A N y i)) = ((@dollar A N y i) = (@dollar A N y i)).
Proof. exact (MK_COMB (@lem7629947 A N i x y h1) (@lem7629948 A N y i)). Qed.
Lemma lem7629951 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7629952 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7629951 A x). Qed.
Lemma lem7629953 {A N : Type'} (y : cart A N) (i : nat) : ((@dollar A N y i) = (@dollar A N y i)) = True.
Proof. exact (@lem7629952 A (@dollar A N y i)). Qed.
Lemma lem7629954 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : ((@dollar A N x i) = (@dollar A N y i)) = True.
Proof. exact (TRANS (@lem7629949 A N i x y h1) (@lem7629953 A N y i)). Qed.
Lemma lem7629955 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : term41 A N x y i.
Proof. exact (fun h0 : term34 N i => @lem7629954 A N i x y h1). Qed.
Lemma lem7629956 {A N : Type'} (x : cart A N) (y : cart A N) (i : nat) : term42 A N x y i.
Proof. exact (@lem7629932 A N x y i True). Qed.
Lemma lem7629957 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (term43 A N x y i) = (term44 N i).
Proof. exact (@lem7629956 A N x y i (@lem7629955 A N i x y h1)). Qed.
Lemma lem7629959 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7629960 {N : Type'} (i : nat) : (term44 N i) = True.
Proof. exact (@lem7629959 (term34 N i)). Qed.
Lemma lem7629961 {A N : Type'} (i : nat) (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (term43 A N x y i) = True.
Proof. exact (TRANS (@lem7629957 A N i x y h1) (@lem7629960 N i)). Qed.
Lemma lem7629962 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (term45 A N x y) = term17.
Proof. exact (fun_ext (fun i : nat => @lem7629961 A N i x y h1)). Qed.
Lemma lem7629963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7629964 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (term3 A N x y) = term18.
Proof. exact (MK_COMB (@lem7629963) (@lem7629962 A N x y h1)). Qed.
Lemma lem7629966 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7629967 (t : Prop) : (term20 t) = t.
Proof. exact (@lem7629966 nat t). Qed.
Lemma lem7629968 : term18 = True.
Proof. exact (@lem7629967 True). Qed.
Lemma lem7629969 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (term3 A N x y) = True.
Proof. exact (TRANS (@lem7629964 A N x y h1) (@lem7629968)). Qed.
Lemma lem7629970 {A N : Type'} (x : cart A N) (y : cart A N) (h1 : term8 A N x y) : (x = y) = True.
Proof. exact (TRANS (@lem7629910 A N x y) (@lem7629969 A N x y h1)). Qed.
Lemma lem7629971 {A N : Type'} (x : cart A N) (y : cart A N) : term46 A N x y.
Proof. exact (fun h0 : term8 A N x y => @lem7629970 A N x y h0). Qed.
Lemma lem7629972 {A N : Type'} (x : cart A N) (y : cart A N) : term47 A N x y.
Proof. exact (@lem7629901 A N x y True). Qed.
Lemma lem7629973 {A N : Type'} (x : cart A N) (y : cart A N) : (term48 A N x y) = (term49 A N x y).
Proof. exact (@lem7629972 A N x y (@lem7629971 A N x y)). Qed.
Lemma lem7629975 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7629976 {A N : Type'} (x : cart A N) (y : cart A N) : (term49 A N x y) = True.
Proof. exact (@lem7629975 (term8 A N x y)). Qed.
Lemma lem7629977 {A N : Type'} (x : cart A N) (y : cart A N) : (term48 A N x y) = True.
Proof. exact (TRANS (@lem7629973 A N x y) (@lem7629976 A N x y)). Qed.
Lemma lem7629978 {A N : Type'} (x : cart A N) (y : cart A N) : True = (term48 A N x y).
Proof. exact (SYM (@lem7629977 A N x y)). Qed.
Lemma lem7629980 {A N : Type'} (x : cart A N) (y : cart A N) : term48 A N x y.
Proof. exact (EQ_MP (@lem7629978 A N x y) (@lem0)). Qed.
Lemma lem7629981 {A N : Type'} (x : cart A N) (y : cart A N) : term50 A N x y.
Proof. exact (conj (@lem7629835 A N x y) (@lem7629980 A N x y)). Qed.
Lemma lem7629982 {A N : Type'} (x : cart A N) (y : cart A N) : (term50 A N x y) = ((x = y) = (term8 A N x y)).
Proof. exact (@lem32 (x = y) (term8 A N x y)). Qed.
Lemma lem7629983 {A N : Type'} (x : cart A N) (y : cart A N) : (x = y) = (term8 A N x y).
Proof. exact (EQ_MP (@lem7629982 A N x y) (@lem7629981 A N x y)). Qed.
Lemma lem7629988 {A N : Type'} (x : cart A N) : term51 A N x.
Proof. exact (fun y : cart A N => @lem7629983 A N x y). Qed.
Lemma lem7629993 {A N : Type'} : term52 A N.
Proof. exact (fun x : cart A N => @lem7629988 A N x). Qed.
