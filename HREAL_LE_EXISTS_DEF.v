Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_LE_EXISTS_DEF_term_abbrevs.
Require Import thm0_spec.
Require Import thm1319607_spec.
Require Import thm1319802_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1321217 (x : hreal) : term0 x.
Proof. exact (@lem1319607 x). Qed.
Lemma lem1321218 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321219 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321218 x) (@lem1321217 x)). Qed.
Lemma lem1321220 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321219 x y). Qed.
Lemma lem1321221 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321222 (x : hreal) (y : hreal) : term3 x y.
Proof. exact (EQ_MP (@lem1321221 x y) (@lem1321220 x y)). Qed.
Lemma lem1321223 (x : hreal) (y : hreal) : (term3 x y) = ((term3 x y) = True).
Proof. exact (@lem7 (term3 x y)). Qed.
Lemma lem1321225 (x : hreal) : term4 x.
Proof. exact (@lem1319802 x). Qed.
Lemma lem1321226 (x : hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1321227 (x : hreal) : term5 x.
Proof. exact (EQ_MP (@lem1321226 x) (@lem1321225 x)). Qed.
Lemma lem1321228 (x : hreal) (y : hreal) : term6 x y.
Proof. exact (@lem1321227 x y). Qed.
Lemma lem1321229 (y : hreal) (x : hreal) : (term6 x y) = (term7 y x).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1321230 (y : hreal) (x : hreal) : term7 y x.
Proof. exact (EQ_MP (@lem1321229 y x) (@lem1321228 x y)). Qed.
Lemma lem1321231 (y : hreal) (x : hreal) : (term7 y x) = ((term7 y x) = True).
Proof. exact (@lem7 (term7 y x)). Qed.
Lemma lem1321234 (y : hreal) (x : hreal) : (term7 y x) = True.
Proof. exact (EQ_MP (@lem1321231 y x) (@lem1321230 y x)). Qed.
Lemma lem1321235 (n : hreal) (m : hreal) : (term7 n m) = True.
Proof. exact (@lem1321234 n m). Qed.
Lemma lem1321236 (n : hreal) (m : hreal) : True = (term7 n m).
Proof. exact (SYM (@lem1321235 n m)). Qed.
Lemma lem1321237 (n : hreal) (m : hreal) : term7 n m.
Proof. exact (EQ_MP (@lem1321236 n m) (@lem0)). Qed.
Lemma lem1321248 (n : hreal) (m : hreal) (h1 : term8 n m) : term8 n m.
Proof. exact (h1). Qed.
Lemma lem1321249 (n : hreal) (m : hreal) (d : hreal) (h1 : n = (hreal_add m d)) : n = (hreal_add m d).
Proof. exact (h1). Qed.
Lemma lem1321250 (m : hreal) : (term9 m) = (term9 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1321251 (n : hreal) (m : hreal) (d : hreal) (h1 : n = (hreal_add m d)) : (term10 m n) = (term11 m d).
Proof. exact (MK_COMB (@lem1321250 m) (@lem1321249 n m d h1)). Qed.
Lemma lem1321252 (m : hreal) (d : hreal) : (term11 m d) = (term3 m d).
Proof. exact (eq_refl (term11 m d)). Qed.
Lemma lem1321253 (m : hreal) (n : hreal) : (term12 m n) = (term12 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1321254 (n : hreal) (m : hreal) (d : hreal) : ((term10 m n) = (term11 m d)) = ((term10 m n) = (term3 m d)).
Proof. exact (MK_COMB (@lem1321253 m n) (@lem1321252 m d)). Qed.
Lemma lem1321255 (m : hreal) (n : hreal) : (term10 m n) = (hreal_le m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1321256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321257 (m : hreal) (n : hreal) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem1321256) (@lem1321255 m n)). Qed.
Lemma lem1321258 (m : hreal) (d : hreal) : (term3 m d) = (term3 m d).
Proof. exact (eq_refl (term3 m d)). Qed.
Lemma lem1321259 (n : hreal) (m : hreal) (d : hreal) : ((term10 m n) = (term3 m d)) = ((hreal_le m n) = (term3 m d)).
Proof. exact (MK_COMB (@lem1321257 m n) (@lem1321258 m d)). Qed.
Lemma lem1321260 (n : hreal) (m : hreal) (d : hreal) : ((term10 m n) = (term11 m d)) = ((hreal_le m n) = (term3 m d)).
Proof. exact (TRANS (@lem1321254 n m d) (@lem1321259 n m d)). Qed.
Lemma lem1321261 (n : hreal) (m : hreal) (d : hreal) (h1 : n = (hreal_add m d)) : (hreal_le m n) = (term3 m d).
Proof. exact (EQ_MP (@lem1321260 n m d) (@lem1321251 n m d h1)). Qed.
Lemma lem1321262 (n : hreal) (m : hreal) (d : hreal) (h1 : n = (hreal_add m d)) : (term3 m d) = (hreal_le m n).
Proof. exact (SYM (@lem1321261 n m d h1)). Qed.
Lemma lem1321264 (x : hreal) (y : hreal) : (term3 x y) = True.
Proof. exact (EQ_MP (@lem1321223 x y) (@lem1321222 x y)). Qed.
Lemma lem1321265 (m : hreal) (d : hreal) : (term3 m d) = True.
Proof. exact (@lem1321264 m d). Qed.
Lemma lem1321266 (m : hreal) (d : hreal) : True = (term3 m d).
Proof. exact (SYM (@lem1321265 m d)). Qed.
Lemma lem1321267 (m : hreal) (d : hreal) : term3 m d.
Proof. exact (EQ_MP (@lem1321266 m d) (@lem0)). Qed.
Lemma lem1321268 (n : hreal) (m : hreal) (d : hreal) (h1 : n = (hreal_add m d)) : hreal_le m n.
Proof. exact (EQ_MP (@lem1321262 n m d h1) (@lem1321267 m d)). Qed.
Lemma lem1321269 (n : hreal) (m : hreal) (h1 : term8 n m) : hreal_le m n.
Proof. exact (ex_elim (@lem1321248 n m h1) (fun d : hreal => fun h0 : term14 n m d => @lem1321268 n m d h0)). Qed.
Lemma lem1321271 (m : hreal) (n : hreal) : term15 m n.
Proof. exact (fun h0 : term8 n m => @lem1321269 n m h0). Qed.
Lemma lem1321272 (m : hreal) (n : hreal) : term16 m n.
Proof. exact (conj (@lem1321237 n m) (@lem1321271 m n)). Qed.
Lemma lem1321273 (n : hreal) (m : hreal) : (term16 m n) = ((hreal_le m n) = (term8 n m)).
Proof. exact (@lem32 (hreal_le m n) (term8 n m)). Qed.
Lemma lem1321274 (n : hreal) (m : hreal) : (hreal_le m n) = (term8 n m).
Proof. exact (EQ_MP (@lem1321273 n m) (@lem1321272 m n)). Qed.
Lemma lem1321279 (m : hreal) : term17 m.
Proof. exact (fun n : hreal => @lem1321274 n m). Qed.
Lemma lem1321284 : term18.
Proof. exact (fun m : hreal => @lem1321279 m). Qed.
