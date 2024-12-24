Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_EXP_term_abbrevs.
Require Import EVEN_MULT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80360_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Lemma lem126078 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem126079 (m : nat) : term1 m.
Proof. exact (@lem126078 (term2 m)). Qed.
Lemma lem126080 (m : nat) : (term3 m) = ((term4 m) = (term5 m)).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem126081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem126082 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem126081) (@lem126080 m)). Qed.
Lemma lem126083 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem126084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem126085 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem126084) (@lem126083 m n)). Qed.
Lemma lem126086 (m : nat) (n : nat) : (term13 m n) = ((term14 m n) = (term15 m n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem126087 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem126085 m n) (@lem126086 m n)). Qed.
Lemma lem126088 (m : nat) : (term18 m) = (term19 m).
Proof. exact (fun_ext (fun n : nat => @lem126087 m n)). Qed.
Lemma lem126089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem126090 (m : nat) : (term20 m) = (term21 m).
Proof. exact (MK_COMB (@lem126089) (@lem126088 m)). Qed.
Lemma lem126091 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem126082 m) (@lem126090 m)). Qed.
Lemma lem126092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem126093 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem126092) (@lem126091 m)). Qed.
Lemma lem126094 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem126095 (m : nat) : (term26 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem126094 m n)). Qed.
Lemma lem126096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem126097 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem126096) (@lem126095 m)). Qed.
Lemma lem126098 (m : nat) : (term1 m) = (term29 m).
Proof. exact (MK_COMB (@lem126093 m) (@lem126097 m)). Qed.
Lemma lem126099 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem126098 m) (@lem126079 m)). Qed.
Lemma lem126130 : term30.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem126131 (m : nat) : term31 m.
Proof. exact (@lem126130 m). Qed.
Lemma lem126132 (m : nat) : (term31 m) = ((term32 m) = term33).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem126134 : term34.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem126135 (n : nat) : term35 n.
Proof. exact (@lem126134 n). Qed.
Lemma lem126136 (n : nat) : (term35 n) = ((term36 n) = (term37 n)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem126142 (m : nat) : (term32 m) = term33.
Proof. exact (EQ_MP (@lem126132 m) (@lem126131 m)). Qed.
Lemma lem126144 : term33 = term38.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem126145 (m : nat) : (term32 m) = term38.
Proof. exact (TRANS (@lem126142 m) (@lem126144)). Qed.
Lemma lem126146 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem126147 (m : nat) : (term4 m) = term39.
Proof. exact (MK_COMB (@lem126146) (@lem126145 m)). Qed.
Lemma lem126149 (n : nat) : (term36 n) = (term37 n).
Proof. exact (EQ_MP (@lem126136 n) (@lem126135 n)). Qed.
Lemma lem126150 : term39 = term40.
Proof. exact (@lem126149 (NUMERAL 0)). Qed.
Lemma lem126152 : term41 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem126153 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem126154 : term40 = (~ True).
Proof. exact (MK_COMB (@lem126153) (@lem126152)). Qed.
Lemma lem126156 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem126157 : term40 = False.
Proof. exact (TRANS (@lem126154) (@lem126156)). Qed.
Lemma lem126158 : term39 = False.
Proof. exact (TRANS (@lem126150) (@lem126157)). Qed.
Lemma lem126159 (m : nat) : (term4 m) = False.
Proof. exact (TRANS (@lem126147 m) (@lem126158)). Qed.
Lemma lem126160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem126161 (m : nat) : (term42 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem126160) (@lem126159 m)). Qed.
Lemma lem126165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem126166 (x : nat) : (x = x) = True.
Proof. exact (@lem126165 nat x). Qed.
Lemma lem126167 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem126166 (NUMERAL 0)). Qed.
Lemma lem126168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem126169 : term43 = (~ True).
Proof. exact (MK_COMB (@lem126168) (@lem126167)). Qed.
Lemma lem126171 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem126172 : term43 = False.
Proof. exact (TRANS (@lem126169) (@lem126171)). Qed.
Lemma lem126173 (m : nat) : (term44 m) = (term44 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem126174 (m : nat) : (term5 m) = (term45 m).
Proof. exact (MK_COMB (@lem126173 m) (@lem126172)). Qed.
Lemma lem126176 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem126177 (m : nat) : (term45 m) = False.
Proof. exact (@lem126176 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem126178 (m : nat) : (term5 m) = False.
Proof. exact (TRANS (@lem126174 m) (@lem126177 m)). Qed.
Lemma lem126179 (m : nat) : ((term4 m) = (term5 m)) = (False = False).
Proof. exact (MK_COMB (@lem126161 m) (@lem126178 m)). Qed.
Lemma lem126181 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem126182 : (False = False) = (~ False).
Proof. exact (@lem126181 False). Qed.
Lemma lem126184 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem126185 : (False = False) = True.
Proof. exact (TRANS (@lem126182) (@lem126184)). Qed.
Lemma lem126186 (m : nat) : ((term4 m) = (term5 m)) = True.
Proof. exact (TRANS (@lem126179 m) (@lem126185)). Qed.
Lemma lem126187 (m : nat) : True = ((term4 m) = (term5 m)).
Proof. exact (SYM (@lem126186 m)). Qed.
Lemma lem126188 (m : nat) : (term4 m) = (term5 m).
Proof. exact (EQ_MP (@lem126187 m) (@lem0)). Qed.
Lemma lem126189 (n : nat) : term46 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem126190 (n : nat) : (term46 n) = (term47 n).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem126191 (n : nat) : term47 n.
Proof. exact (EQ_MP (@lem126190 n) (@lem126189 n)). Qed.
Lemma lem126192 (n : nat) : term48 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem126205 (m : nat) : term49 m.
Proof. exact (@lem126076 m). Qed.
Lemma lem126206 (m : nat) : (term49 m) = (term50 m).
Proof. exact (eq_refl (term49 m)). Qed.
Lemma lem126207 (m : nat) : term50 m.
Proof. exact (EQ_MP (@lem126206 m) (@lem126205 m)). Qed.
Lemma lem126208 (m : nat) (n : nat) : term51 m n.
Proof. exact (@lem126207 m n). Qed.
Lemma lem126209 (m : nat) (n : nat) : (term51 m n) = ((term52 m n) = (term53 m n)).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem126211 : term54.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem126212 (m : nat) : term55 m.
Proof. exact (@lem126211 m). Qed.
Lemma lem126213 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem126214 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem126213 m) (@lem126212 m)). Qed.
Lemma lem126215 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem126214 m n). Qed.
Lemma lem126216 (m : nat) (n : nat) : (term57 m n) = ((term58 m n) = (term59 m n)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem126230 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (EQ_MP (@lem126216 m n) (@lem126215 m n)). Qed.
Lemma lem126231 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem126232 (m : nat) (n : nat) : (term14 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem126231) (@lem126230 m n)). Qed.
Lemma lem126234 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (EQ_MP (@lem126209 m n) (@lem126208 m n)). Qed.
Lemma lem126235 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (@lem126234 m (Nat.pow m n)). Qed.
Lemma lem126239 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term9 m n) = (term10 m n).
Proof. exact (h1). Qed.
Lemma lem126244 (m : nat) : (term62 m) = (term62 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem126245 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term61 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem126244 m) (@lem126239 m n h1)). Qed.
Lemma lem126248 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term60 m n) = (term63 m n).
Proof. exact (TRANS (@lem126235 m n) (@lem126245 m n h1)). Qed.
Lemma lem126249 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term14 m n) = (term63 m n).
Proof. exact (TRANS (@lem126232 m n) (@lem126248 m n h1)). Qed.
Lemma lem126250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem126251 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term64 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem126250) (@lem126249 m n h1)). Qed.
Lemma lem126255 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem126192 n (@lem126191 n)). Qed.
Lemma lem126256 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem126257 (n : nat) : (term47 n) = (~ False).
Proof. exact (MK_COMB (@lem126256) (@lem126255 n)). Qed.
Lemma lem126259 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem126260 (n : nat) : (term47 n) = True.
Proof. exact (TRANS (@lem126257 n) (@lem126259)). Qed.
Lemma lem126261 (m : nat) : (term44 m) = (term44 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem126262 (n : nat) (m : nat) : (term15 m n) = (term66 m).
Proof. exact (MK_COMB (@lem126261 m) (@lem126260 n)). Qed.
Lemma lem126264 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem126265 (m : nat) : (term66 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem126264 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem126266 (n : nat) (m : nat) : (term15 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem126262 n m) (@lem126265 m)). Qed.
Lemma lem126267 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : ((term14 m n) = (term15 m n)) = ((term63 m n) = (Coq.Arith.PeanoNat.Nat.Even m)).
Proof. exact (MK_COMB (@lem126251 m n h1) (@lem126266 n m)). Qed.
Lemma lem126270 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : ((term63 m n) = (Coq.Arith.PeanoNat.Nat.Even m)) = ((term14 m n) = (term15 m n)).
Proof. exact (SYM (@lem126267 m n h1)). Qed.
Lemma lem126271 (m : nat) (n : nat) (h1 : term63 m n) : term63 m n.
Proof. exact (h1). Qed.
Lemma lem126272 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem126273 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem126275 (m : nat) (n : nat) (h1 : term10 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (proj1 (@lem126273 m n h1)). Qed.
Lemma lem126276 (m : nat) (n : nat) (h1 : term63 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (or_elim (@lem126271 m n h1) (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem126272 m h0) (fun h0 : term10 m n => @lem126275 m n h0)). Qed.
Lemma lem126277 (n : nat) (m : nat) : term67 n m.
Proof. exact (fun h0 : term63 m n => @lem126276 m n h0). Qed.
Lemma lem126278 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem126279 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : term63 m n.
Proof. exact (or_intro1 (@lem126278 m h1) (term10 m n)). Qed.
Lemma lem126280 (m : nat) (n : nat) : term68 m n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem126279 n m h0). Qed.
Lemma lem126281 (m : nat) (n : nat) : term69 m n.
Proof. exact (conj (@lem126277 n m) (@lem126280 m n)). Qed.
Lemma lem126282 (n : nat) (m : nat) : (term69 m n) = ((term63 m n) = (Coq.Arith.PeanoNat.Nat.Even m)).
Proof. exact (@lem32 (term63 m n) (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem126283 (n : nat) (m : nat) : (term63 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (EQ_MP (@lem126282 n m) (@lem126281 m n)). Qed.
Lemma lem126284 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term14 m n) = (term15 m n).
Proof. exact (EQ_MP (@lem126270 m n h1) (@lem126283 n m)). Qed.
Lemma lem126285 (m : nat) (n : nat) : term17 m n.
Proof. exact (fun h0 : (term9 m n) = (term10 m n) => @lem126284 m n h0). Qed.
Lemma lem126290 (m : nat) : term21 m.
Proof. exact (fun n : nat => @lem126285 m n). Qed.
Lemma lem126291 (m : nat) : term23 m.
Proof. exact (conj (@lem126188 m) (@lem126290 m)). Qed.
Lemma lem126292 (m : nat) : term28 m.
Proof. exact (@lem126099 m (@lem126291 m)). Qed.
Lemma lem126297 : term70.
Proof. exact (fun m : nat => @lem126292 m). Qed.
