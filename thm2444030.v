Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2444030_term_abbrevs.
Require Import INT_SUB_0_spec.
Lemma lem2444015 (x : int) (y : int) (h1 : ((int_sub x y) = term0) = (x = y)) : ((int_sub x y) = term0) = (x = y).
Proof. exact (h1). Qed.
Lemma lem2444016 (x : int) (y : int) (h1 : ((int_sub x y) = term0) = (x = y)) : (x = y) = ((int_sub x y) = term0).
Proof. exact (SYM (@lem2444015 x y h1)). Qed.
Lemma lem2444017 (x : int) (y : int) (h1 : (x = y) = ((int_sub x y) = term0)) : (x = y) = ((int_sub x y) = term0).
Proof. exact (h1). Qed.
Lemma lem2444018 (x : int) (y : int) (h1 : (x = y) = ((int_sub x y) = term0)) : ((int_sub x y) = term0) = (x = y).
Proof. exact (SYM (@lem2444017 x y h1)). Qed.
Lemma lem2444019 (x : int) (y : int) : (((int_sub x y) = term0) = (x = y)) = ((x = y) = ((int_sub x y) = term0)).
Proof. exact (prop_ext (fun h1 : ((int_sub x y) = term0) = (x = y) => @lem2444016 x y h1) (fun h1 : (x = y) = ((int_sub x y) = term0) => @lem2444018 x y h1)). Qed.
Lemma lem2444020 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2444019 x y)). Qed.
Lemma lem2444021 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2444022 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2444021) (@lem2444020 x)). Qed.
Lemma lem2444023 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2444022 x)). Qed.
Lemma lem2444024 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2444025 : term7 = term8.
Proof. exact (MK_COMB (@lem2444024) (@lem2444023)). Qed.
Lemma lem2444026 : term8.
Proof. exact (EQ_MP (@lem2444025) (@lem2310063)). Qed.
Lemma lem2444027 (x : int) : term9 x.
Proof. exact (@lem2444026 x). Qed.
Lemma lem2444028 (x : int) : (term9 x) = (term4 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2444029 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2444028 x) (@lem2444027 x)). Qed.
Lemma lem2444030 (x : int) (y : int) : term10 x y.
Proof. exact (@lem2444029 x y). Qed.
