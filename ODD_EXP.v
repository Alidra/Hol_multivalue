Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_EXP_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import ODD_MULT_spec.
Require Import thm0_spec.
Require Import thm124616_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80360_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Lemma lem128117 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem128118 (m : nat) : term1 m.
Proof. exact (@lem128117 (term2 m)). Qed.
Lemma lem128119 (m : nat) : (term3 m) = ((term4 m) = (term5 m)).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem128120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem128121 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem128120) (@lem128119 m)). Qed.
Lemma lem128122 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem128123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128124 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem128123) (@lem128122 m n)). Qed.
Lemma lem128125 (m : nat) (n : nat) : (term13 m n) = ((term14 m n) = (term15 m n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem128126 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem128124 m n) (@lem128125 m n)). Qed.
Lemma lem128127 (m : nat) : (term18 m) = (term19 m).
Proof. exact (fun_ext (fun n : nat => @lem128126 m n)). Qed.
Lemma lem128128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128129 (m : nat) : (term20 m) = (term21 m).
Proof. exact (MK_COMB (@lem128128) (@lem128127 m)). Qed.
Lemma lem128130 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem128121 m) (@lem128129 m)). Qed.
Lemma lem128131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128132 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem128131) (@lem128130 m)). Qed.
Lemma lem128133 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem128134 (m : nat) : (term26 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem128133 m n)). Qed.
Lemma lem128135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128136 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem128135) (@lem128134 m)). Qed.
Lemma lem128137 (m : nat) : (term1 m) = (term29 m).
Proof. exact (MK_COMB (@lem128132 m) (@lem128136 m)). Qed.
Lemma lem128138 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem128137 m) (@lem128118 m)). Qed.
Lemma lem128169 : term30.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem128170 (m : nat) : term31 m.
Proof. exact (@lem128169 m). Qed.
Lemma lem128171 (m : nat) : (term31 m) = ((term32 m) = term33).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem128173 : term34.
Proof. exact (proj2 (@lem124616)). Qed.
Lemma lem128174 (n : nat) : term35 n.
Proof. exact (@lem128173 n). Qed.
Lemma lem128175 (n : nat) : (term35 n) = ((term36 n) = (term37 n)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem128181 (m : nat) : (term32 m) = term33.
Proof. exact (EQ_MP (@lem128171 m) (@lem128170 m)). Qed.
Lemma lem128183 : term33 = term38.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem128184 (m : nat) : (term32 m) = term38.
Proof. exact (TRANS (@lem128181 m) (@lem128183)). Qed.
Lemma lem128185 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem128186 (m : nat) : (term4 m) = term39.
Proof. exact (MK_COMB (@lem128185) (@lem128184 m)). Qed.
Lemma lem128188 (n : nat) : (term36 n) = (term37 n).
Proof. exact (EQ_MP (@lem128175 n) (@lem128174 n)). Qed.
Lemma lem128189 : term39 = term40.
Proof. exact (@lem128188 (NUMERAL 0)). Qed.
Lemma lem128191 : term41 = False.
Proof. exact (proj1 (@lem124616)). Qed.
Lemma lem128192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem128193 : term40 = (~ False).
Proof. exact (MK_COMB (@lem128192) (@lem128191)). Qed.
Lemma lem128195 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem128196 : term40 = True.
Proof. exact (TRANS (@lem128193) (@lem128195)). Qed.
Lemma lem128197 : term39 = True.
Proof. exact (TRANS (@lem128189) (@lem128196)). Qed.
Lemma lem128198 (m : nat) : (term4 m) = True.
Proof. exact (TRANS (@lem128186 m) (@lem128197)). Qed.
Lemma lem128199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem128200 (m : nat) : (term42 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem128199) (@lem128198 m)). Qed.
Lemma lem128204 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem128205 (x : nat) : (x = x) = True.
Proof. exact (@lem128204 nat x). Qed.
Lemma lem128206 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem128205 (NUMERAL 0)). Qed.
Lemma lem128207 (m : nat) : (term43 m) = (term43 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem128208 (m : nat) : (term5 m) = (term44 m).
Proof. exact (MK_COMB (@lem128207 m) (@lem128206)). Qed.
Lemma lem128210 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem128211 (m : nat) : (term44 m) = True.
Proof. exact (@lem128210 (Coq.Arith.PeanoNat.Nat.Odd m)). Qed.
Lemma lem128212 (m : nat) : (term5 m) = True.
Proof. exact (TRANS (@lem128208 m) (@lem128211 m)). Qed.
Lemma lem128213 (m : nat) : ((term4 m) = (term5 m)) = (True = True).
Proof. exact (MK_COMB (@lem128200 m) (@lem128212 m)). Qed.
Lemma lem128215 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem128216 : (True = True) = True.
Proof. exact (@lem128215 True). Qed.
Lemma lem128217 (m : nat) : ((term4 m) = (term5 m)) = True.
Proof. exact (TRANS (@lem128213 m) (@lem128216)). Qed.
Lemma lem128218 (m : nat) : True = ((term4 m) = (term5 m)).
Proof. exact (SYM (@lem128217 m)). Qed.
Lemma lem128219 (m : nat) : (term4 m) = (term5 m).
Proof. exact (EQ_MP (@lem128218 m) (@lem0)). Qed.
Lemma lem128220 (n : nat) : term45 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem128221 (n : nat) : (term45 n) = (term46 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem128222 (n : nat) : term46 n.
Proof. exact (EQ_MP (@lem128221 n) (@lem128220 n)). Qed.
Lemma lem128223 (n : nat) : term47 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem128236 (m : nat) : term48 m.
Proof. exact (@lem128115 m). Qed.
Lemma lem128237 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem128238 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem128237 m) (@lem128236 m)). Qed.
Lemma lem128239 (m : nat) (n : nat) : term50 m n.
Proof. exact (@lem128238 m n). Qed.
Lemma lem128240 (m : nat) (n : nat) : (term50 m n) = ((term51 m n) = (term52 m n)).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem128242 : term53.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem128243 (m : nat) : term54 m.
Proof. exact (@lem128242 m). Qed.
Lemma lem128244 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem128245 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem128244 m) (@lem128243 m)). Qed.
Lemma lem128246 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem128245 m n). Qed.
Lemma lem128247 (m : nat) (n : nat) : (term56 m n) = ((term57 m n) = (term58 m n)).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem128261 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (EQ_MP (@lem128247 m n) (@lem128246 m n)). Qed.
Lemma lem128262 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem128263 (m : nat) (n : nat) : (term14 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem128262) (@lem128261 m n)). Qed.
Lemma lem128265 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (EQ_MP (@lem128240 m n) (@lem128239 m n)). Qed.
Lemma lem128266 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (@lem128265 m (Nat.pow m n)). Qed.
Lemma lem128270 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term9 m n) = (term10 m n).
Proof. exact (h1). Qed.
Lemma lem128275 (m : nat) : (term61 m) = (term61 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem128276 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term60 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem128275 m) (@lem128270 m n h1)). Qed.
Lemma lem128279 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term59 m n) = (term62 m n).
Proof. exact (TRANS (@lem128266 m n) (@lem128276 m n h1)). Qed.
Lemma lem128280 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term14 m n) = (term62 m n).
Proof. exact (TRANS (@lem128263 m n) (@lem128279 m n h1)). Qed.
Lemma lem128281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem128282 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term63 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem128281) (@lem128280 m n h1)). Qed.
Lemma lem128286 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem128223 n (@lem128222 n)). Qed.
Lemma lem128287 (m : nat) : (term43 m) = (term43 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem128288 (n : nat) (m : nat) : (term15 m n) = (term65 m).
Proof. exact (MK_COMB (@lem128287 m) (@lem128286 n)). Qed.
Lemma lem128290 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem128291 (m : nat) : (term65 m) = (Coq.Arith.PeanoNat.Nat.Odd m).
Proof. exact (@lem128290 (Coq.Arith.PeanoNat.Nat.Odd m)). Qed.
Lemma lem128292 (n : nat) (m : nat) : (term15 m n) = (Coq.Arith.PeanoNat.Nat.Odd m).
Proof. exact (TRANS (@lem128288 n m) (@lem128291 m)). Qed.
Lemma lem128293 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : ((term14 m n) = (term15 m n)) = ((term62 m n) = (Coq.Arith.PeanoNat.Nat.Odd m)).
Proof. exact (MK_COMB (@lem128282 m n h1) (@lem128292 n m)). Qed.
Lemma lem128296 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : ((term62 m n) = (Coq.Arith.PeanoNat.Nat.Odd m)) = ((term14 m n) = (term15 m n)).
Proof. exact (SYM (@lem128293 m n h1)). Qed.
Lemma lem128297 (m : nat) (n : nat) (h1 : term62 m n) : term62 m n.
Proof. exact (h1). Qed.
Lemma lem128299 (m : nat) (n : nat) (h1 : term62 m n) : Coq.Arith.PeanoNat.Nat.Odd m.
Proof. exact (proj1 (@lem128297 m n h1)). Qed.
Lemma lem128300 (n : nat) (m : nat) : term66 n m.
Proof. exact (fun h0 : term62 m n => @lem128299 m n h0). Qed.
Lemma lem128301 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd m) : Coq.Arith.PeanoNat.Nat.Odd m.
Proof. exact (h1). Qed.
Lemma lem128302 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd m) : term10 m n.
Proof. exact (or_intro1 (@lem128301 m h1) (n = (NUMERAL 0))). Qed.
Lemma lem128303 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd m) : term62 m n.
Proof. exact (conj (@lem128301 m h1) (@lem128302 n m h1)). Qed.
Lemma lem128304 (m : nat) (n : nat) : term67 m n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd m => @lem128303 n m h0). Qed.
Lemma lem128305 (m : nat) (n : nat) : term68 m n.
Proof. exact (conj (@lem128300 n m) (@lem128304 m n)). Qed.
Lemma lem128306 (n : nat) (m : nat) : (term68 m n) = ((term62 m n) = (Coq.Arith.PeanoNat.Nat.Odd m)).
Proof. exact (@lem32 (term62 m n) (Coq.Arith.PeanoNat.Nat.Odd m)). Qed.
Lemma lem128307 (n : nat) (m : nat) : (term62 m n) = (Coq.Arith.PeanoNat.Nat.Odd m).
Proof. exact (EQ_MP (@lem128306 n m) (@lem128305 m n)). Qed.
Lemma lem128308 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term14 m n) = (term15 m n).
Proof. exact (EQ_MP (@lem128296 m n h1) (@lem128307 n m)). Qed.
Lemma lem128309 (m : nat) (n : nat) : term17 m n.
Proof. exact (fun h0 : (term9 m n) = (term10 m n) => @lem128308 m n h0). Qed.
Lemma lem128314 (m : nat) : term21 m.
Proof. exact (fun n : nat => @lem128309 m n). Qed.
Lemma lem128315 (m : nat) : term23 m.
Proof. exact (conj (@lem128219 m) (@lem128314 m)). Qed.
Lemma lem128316 (m : nat) : term28 m.
Proof. exact (@lem128138 m (@lem128315 m)). Qed.
Lemma lem128321 : term69.
Proof. exact (fun m : nat => @lem128316 m). Qed.
