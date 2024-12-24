Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_CLAUSES_term_abbrevs.
Require Import DIMINDEX_UNIQUE_spec.
Require Import HAS_SIZE_1_spec.
Require Import HAS_SIZE_TYBIT0_spec.
Require Import HAS_SIZE_TYBIT1_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm7603427_spec.
Lemma lem7933120 {A : Type'} : (term0 A) = ((term0 A) = True).
Proof. exact (@lem7 (term0 A)). Qed.
Lemma lem7933122 {A : Type'} : (term1 A) = ((term1 A) = True).
Proof. exact (@lem7 (term1 A)). Qed.
Lemma lem7933124 {A : Type'} (n : nat) (h1 : term2 A n) : term2 A n.
Proof. exact (h1). Qed.
Lemma lem7933125 {A : Type'} (n : nat) (h1 : @HAS_SIZE A (@UNIV A) n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (h1). Qed.
Lemma lem7933126 {A : Type'} (n : nat) (h1 : term2 A n) (h2 : @HAS_SIZE A (@UNIV A) n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7933124 A n h1 (@lem7933125 A n h2)). Qed.
Lemma lem7933127 {A : Type'} (n : nat) (h1 : @HAS_SIZE A (@UNIV A) n) : term3 A n.
Proof. exact (fun h0 : term2 A n => @lem7933126 A n h0 h1). Qed.
Lemma lem7933128 {A : Type'} (n : nat) (h1 : term2 A n) : term2 A n.
Proof. exact (h1). Qed.
Lemma lem7933129 {A : Type'} (n : nat) (h1 : term2 A n) (h2 : @HAS_SIZE A (@UNIV A) n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7933127 A n h2 (@lem7933128 A n h1)). Qed.
Lemma lem7933130 {A : Type'} (n : nat) (h1 : term2 A n) : term2 A n.
Proof. exact (fun h0 : @HAS_SIZE A (@UNIV A) n => @lem7933129 A n h1 h0). Qed.
Lemma lem7933131 {A : Type'} (n : nat) : term4 A n.
Proof. exact (fun h0 : term2 A n => @lem7933130 A n h0). Qed.
Lemma lem7933138 : (@dimindex unit (@UNIV unit)) = term5.
Proof. exact (@lem7603427 (@lem7603370)). Qed.
Lemma lem7933139 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7933140 : term6 = term7.
Proof. exact (MK_COMB (@lem7933139) (@lem7933138)). Qed.
Lemma lem7933141 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem7933142 : ((@dimindex unit (@UNIV unit)) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem7933140) (@lem7933141)). Qed.
Lemma lem7933144 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7933145 (x : nat) : (x = x) = True.
Proof. exact (@lem7933144 nat x). Qed.
Lemma lem7933146 : (term5 = term5) = True.
Proof. exact (@lem7933145 term5). Qed.
Lemma lem7933147 : ((@dimindex unit (@UNIV unit)) = term5) = True.
Proof. exact (TRANS (@lem7933142) (@lem7933146)). Qed.
Lemma lem7933148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933149 : term8 = (and True).
Proof. exact (MK_COMB (@lem7933148) (@lem7933147)). Qed.
Lemma lem7933164 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem7933165 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem7933149) (@lem7933164 A)). Qed.
Lemma lem7933167 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7933168 {A : Type'} : (term11 A) = (term9 A).
Proof. exact (@lem7933167 (term9 A)). Qed.
Lemma lem7933183 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (TRANS (@lem7933165 A) (@lem7933168 A)). Qed.
Lemma lem7933184 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (SYM (@lem7933183 A)). Qed.
Lemma lem7933186 {A : Type'} (n : nat) : term2 A n.
Proof. exact (@lem7933131 A n (@lem7598120 A n)). Qed.
Lemma lem7933187 {A : Type'} (n : nat) : term12 A n.
Proof. exact (@lem7933186 (tybit0 A) n). Qed.
Lemma lem7933188 {A : Type'} : term13 A.
Proof. exact (@lem7933187 A (term14 A)). Qed.
Lemma lem7933190 {A : Type'} (n : nat) : term2 A n.
Proof. exact (@lem7933131 A n (@lem7598120 A n)). Qed.
Lemma lem7933191 {A : Type'} (n : nat) : term15 A n.
Proof. exact (@lem7933190 (tybit1 A) n). Qed.
Lemma lem7933192 {A : Type'} : term16 A.
Proof. exact (@lem7933191 A (term17 A)). Qed.
Lemma lem7933194 {A : Type'} : (term1 A) = True.
Proof. exact (EQ_MP (@lem7933122 A) (@lem7932264 A)). Qed.
Lemma lem7933195 {A : Type'} : True = (term1 A).
Proof. exact (SYM (@lem7933194 A)). Qed.
Lemma lem7933196 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem7933195 A) (@lem0)). Qed.
Lemma lem7933198 {A : Type'} : (term0 A) = True.
Proof. exact (EQ_MP (@lem7933120 A) (@lem7933087 A)). Qed.
Lemma lem7933199 {A : Type'} : True = (term0 A).
Proof. exact (SYM (@lem7933198 A)). Qed.
Lemma lem7933200 {A : Type'} : term0 A.
Proof. exact (EQ_MP (@lem7933199 A) (@lem0)). Qed.
Lemma lem7933201 {A : Type'} : (@dimindex (tybit1 A) (@UNIV (tybit1 A))) = (term17 A).
Proof. exact (@lem7933192 A (@lem7933200 A)). Qed.
Lemma lem7933202 {A : Type'} : (@dimindex (tybit0 A) (@UNIV (tybit0 A))) = (term14 A).
Proof. exact (@lem7933188 A (@lem7933196 A)). Qed.
Lemma lem7933203 {A : Type'} : term9 A.
Proof. exact (conj (@lem7933202 A) (@lem7933201 A)). Qed.
Lemma lem7933204 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem7933184 A) (@lem7933203 A)). Qed.
