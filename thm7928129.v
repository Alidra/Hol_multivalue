Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928129_term_abbrevs.
Require Import thm32_spec.
Require Import tybit0_RECURSION_spec.
Lemma lem7928061 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (h1). Qed.
Lemma lem7928062 {A : Type'} (a : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : term1 A _103800 a.
Proof. exact (@lem7928061 A _103800 h1 a). Qed.
Lemma lem7928063 {A : Type'} (_103800 : type1342 A) (a : finite_sum A A) : (term1 A _103800 a) = ((term2 A _103800 a) = a).
Proof. exact (eq_refl (term1 A _103800 a)). Qed.
Lemma lem7928064 {A : Type'} (a : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : (term2 A _103800 a) = a.
Proof. exact (EQ_MP (@lem7928063 A _103800 a) (@lem7928062 A a _103800 h1)). Qed.
Lemma lem7928065 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (fun a : finite_sum A A => @lem7928064 A a _103800 h1). Qed.
Lemma lem7928066 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (h1). Qed.
Lemma lem7928067 {A : Type'} (_103800 : type1342 A) : (term0 A _103800) = (term0 A _103800).
Proof. exact (prop_ext (fun h1 : term0 A _103800 => @lem7928065 A _103800 h1) (fun h1 : term0 A _103800 => @lem7928066 A _103800 h1)). Qed.
Lemma lem7928068 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (EQ_MP (@lem7928067 A _103800) (@lem7928066 A _103800 h1)). Qed.
Lemma lem7928069 {A Z : Type'} (f : type47 A Z) : term3 A Z f.
Proof. exact (@lem7927999 A Z f). Qed.
Lemma lem7928070 {A Z : Type'} (f : type47 A Z) : (term3 A Z f) = (term4 A Z f).
Proof. exact (eq_refl (term3 A Z f)). Qed.
Lemma lem7928071 {A Z : Type'} (f : type47 A Z) : term4 A Z f.
Proof. exact (EQ_MP (@lem7928070 A Z f) (@lem7928069 A Z f)). Qed.
Lemma lem7928072 {A : Type'} (f : type43 A) : term5 A f.
Proof. exact (@lem7928071 A (finite_sum A A) f). Qed.
Lemma lem7928073 {A : Type'} : term6 A.
Proof. exact (@lem7928072 A (term7 A)). Qed.
Lemma lem7928074 {A : Type'} (a : finite_sum A A) : (term8 A a) = a.
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem7928075 {A : Type'} (fn : type1342 A) (a : finite_sum A A) : (term9 A fn a) = (term9 A fn a).
Proof. exact (eq_refl (term9 A fn a)). Qed.
Lemma lem7928076 {A : Type'} (fn : type1342 A) (a : finite_sum A A) : ((term2 A fn a) = (term8 A a)) = ((term2 A fn a) = a).
Proof. exact (MK_COMB (@lem7928075 A fn a) (@lem7928074 A a)). Qed.
Lemma lem7928077 {A : Type'} (fn : type1342 A) : (term10 A fn) = (term11 A fn).
Proof. exact (fun_ext (fun a : finite_sum A A => @lem7928076 A fn a)). Qed.
Lemma lem7928078 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7928079 {A : Type'} (fn : type1342 A) : (term12 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem7928078 A) (@lem7928077 A fn)). Qed.
Lemma lem7928080 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun fn : type1342 A => @lem7928079 A fn)). Qed.
Lemma lem7928081 {A : Type'} : (@ex ((tybit0 A) -> finite_sum A A)) = (@ex ((tybit0 A) -> finite_sum A A)).
Proof. exact (eq_refl (@ex ((tybit0 A) -> finite_sum A A))). Qed.
Lemma lem7928082 {A : Type'} : (term6 A) = (term15 A).
Proof. exact (MK_COMB (@lem7928081 A) (@lem7928080 A)). Qed.
Lemma lem7928083 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7928082 A) (@lem7928073 A)). Qed.
Lemma lem7928084 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (h1). Qed.
Lemma lem7928085 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term15 A.
Proof. exact (ex_intro (term14 A) _103800 (@lem7928084 A _103800 h1)). Qed.
Lemma lem7928086 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7928087 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (ex_elim (@lem7928086 A h1) (fun _103800 : type1342 A => fun h0 : term14 A _103800 => @lem7928085 A _103800 h0)). Qed.
Lemma lem7928088 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7928087 A h1) (fun h1 : term15 A => @lem7928083 A)). Qed.
Lemma lem7928089 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7928088 A) (@lem7928083 A)). Qed.
Lemma lem7928090 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term15 A.
Proof. exact (ex_intro (term14 A) _103800 (@lem7928068 A _103800 h1)). Qed.
Lemma lem7928091 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7928092 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (ex_elim (@lem7928091 A h1) (fun _103800 : type1342 A => fun h0 : term14 A _103800 => @lem7928090 A _103800 h0)). Qed.
Lemma lem7928093 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7928092 A h1) (fun h1 : term15 A => @lem7928089 A)). Qed.
Lemma lem7928094 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7928093 A) (@lem7928089 A)). Qed.
Lemma lem7928097 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (h1). Qed.
Lemma lem7928098 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term15 A.
Proof. exact (ex_intro (term14 A) _103800 (@lem7928097 A _103800 h1)). Qed.
Lemma lem7928099 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7928100 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (ex_elim (@lem7928099 A h1) (fun _103800 : type1342 A => fun h0 : term14 A _103800 => @lem7928098 A _103800 h0)). Qed.
Lemma lem7928101 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7928100 A h1) (fun h1 : term15 A => @lem7928094 A)). Qed.
Lemma lem7928102 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7928101 A) (@lem7928094 A)). Qed.
Lemma lem7928103 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) (h1 : (@mktybit0 A a) = (@mktybit0 A a')) : (@mktybit0 A a) = (@mktybit0 A a').
Proof. exact (h1). Qed.
Lemma lem7928104 {A : Type'} (_103800 : type1342 A) : _103800 = _103800.
Proof. exact (eq_refl _103800). Qed.
Lemma lem7928105 {A : Type'} (_103800 : type1342 A) (a : finite_sum A A) (a' : finite_sum A A) (h1 : (@mktybit0 A a) = (@mktybit0 A a')) : (term2 A _103800 a) = (term2 A _103800 a').
Proof. exact (MK_COMB (@lem7928104 A _103800) (@lem7928103 A a a' h1)). Qed.
Lemma lem7928106 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term0 A _103800.
Proof. exact (h1). Qed.
Lemma lem7928107 {A : Type'} (a : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : term1 A _103800 a.
Proof. exact (@lem7928106 A _103800 h1 a). Qed.
Lemma lem7928108 {A : Type'} (_103800 : type1342 A) (a : finite_sum A A) : (term1 A _103800 a) = ((term2 A _103800 a) = a).
Proof. exact (eq_refl (term1 A _103800 a)). Qed.
Lemma lem7928109 {A : Type'} (a : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : (term2 A _103800 a) = a.
Proof. exact (EQ_MP (@lem7928108 A _103800 a) (@lem7928107 A a _103800 h1)). Qed.
Lemma lem7928110 {A : Type'} (a' : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : (term2 A _103800 a') = a'.
Proof. exact (@lem7928109 A a' _103800 h1). Qed.
Lemma lem7928111 {A : Type'} (a : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : a = (term2 A _103800 a).
Proof. exact (SYM (@lem7928109 A a _103800 h1)). Qed.
Lemma lem7928112 {A : Type'} (_103800 : type1342 A) (a : finite_sum A A) (a' : finite_sum A A) (h1 : term0 A _103800) (h2 : (@mktybit0 A a) = (@mktybit0 A a')) : a = (term2 A _103800 a').
Proof. exact (TRANS (@lem7928111 A a _103800 h1) (@lem7928105 A _103800 a a' h2)). Qed.
Lemma lem7928115 {A : Type'} (_103800 : type1342 A) (a : finite_sum A A) (a' : finite_sum A A) (h1 : term0 A _103800) (h2 : (@mktybit0 A a) = (@mktybit0 A a')) : a = a'.
Proof. exact (TRANS (@lem7928112 A _103800 a a' h1 h2) (@lem7928110 A a' _103800 h1)). Qed.
Lemma lem7928116 {A : Type'} : (@mktybit0 A) = (@mktybit0 A).
Proof. exact (eq_refl (@mktybit0 A)). Qed.
Lemma lem7928117 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) (h1 : a = a') : a = a'.
Proof. exact (h1). Qed.
Lemma lem7928118 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) (h1 : a = a') : (@mktybit0 A a) = (@mktybit0 A a').
Proof. exact (MK_COMB (@lem7928116 A) (@lem7928117 A a a' h1)). Qed.
Lemma lem7928119 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : term16 A a a'.
Proof. exact (fun h0 : a = a' => @lem7928118 A a a' h0). Qed.
Lemma lem7928120 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : term17 A a a'.
Proof. exact (fun h0 : (@mktybit0 A a) = (@mktybit0 A a') => @lem7928115 A _103800 a a' h1 h0). Qed.
Lemma lem7928121 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : term18 A a a'.
Proof. exact (conj (@lem7928120 A a a' _103800 h1) (@lem7928119 A a a')). Qed.
Lemma lem7928122 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : (term18 A a a') = (((@mktybit0 A a) = (@mktybit0 A a')) = (a = a')).
Proof. exact (@lem32 ((@mktybit0 A a) = (@mktybit0 A a')) (a = a')). Qed.
Lemma lem7928123 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : ((@mktybit0 A a) = (@mktybit0 A a')) = (a = a').
Proof. exact (EQ_MP (@lem7928122 A a a') (@lem7928121 A a a' _103800 h1)). Qed.
Lemma lem7928124 {A : Type'} (a : finite_sum A A) (_103800 : type1342 A) (h1 : term0 A _103800) : term19 A a.
Proof. exact (fun a' : finite_sum A A => @lem7928123 A a a' _103800 h1). Qed.
Lemma lem7928125 {A : Type'} (_103800 : type1342 A) (h1 : term0 A _103800) : term20 A.
Proof. exact (fun a : finite_sum A A => @lem7928124 A a _103800 h1). Qed.
Lemma lem7928126 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7928127 {A : Type'} (h1 : term15 A) : term20 A.
Proof. exact (ex_elim (@lem7928126 A h1) (fun _103800 : type1342 A => fun h0 : term14 A _103800 => @lem7928125 A _103800 h0)). Qed.
Lemma lem7928128 {A : Type'} : (term15 A) = (term20 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7928127 A h1) (fun h1 : term20 A => @lem7928102 A)). Qed.
Lemma lem7928129 {A : Type'} : term20 A.
Proof. exact (EQ_MP (@lem7928128 A) (@lem7928102 A)). Qed.
