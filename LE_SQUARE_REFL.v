Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_SQUARE_REFL_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_ADDR_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem106180 (m : nat) : term0 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem106181 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem106182 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem106181 m) (@lem106180 m)). Qed.
Lemma lem106183 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem106182 m n). Qed.
Lemma lem106184 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem106185 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem106184 m n) (@lem106183 m n)). Qed.
Lemma lem106186 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem106188 (n : nat) : term4 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem106189 (n : nat) : (term4 n) = (term5 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem106190 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem106189 n) (@lem106188 n)). Qed.
Lemma lem106191 (n : nat) : (term5 n) = ((term5 n) = True).
Proof. exact (@lem7 (term5 n)). Qed.
Lemma lem106193 : term6.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem106194 : term7.
Proof. exact (proj2 (@lem106193)). Qed.
Lemma lem106195 : term8.
Proof. exact (proj2 (@lem106194)). Qed.
Lemma lem106196 : term9.
Proof. exact (proj2 (@lem106195)). Qed.
Lemma lem106197 : term10.
Proof. exact (proj2 (@lem106196)). Qed.
Lemma lem106198 (m : nat) : term11 m.
Proof. exact (@lem106197 m). Qed.
Lemma lem106199 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem106200 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem106199 m) (@lem106198 m)). Qed.
Lemma lem106201 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem106200 m n). Qed.
Lemma lem106202 (m : nat) (n : nat) : (term13 m n) = ((term14 m n) = (term15 m n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem106204 : term16.
Proof. exact (proj1 (@lem106196)). Qed.
Lemma lem106205 (m : nat) : term17 m.
Proof. exact (@lem106204 m). Qed.
Lemma lem106206 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem106207 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem106206 m) (@lem106205 m)). Qed.
Lemma lem106208 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem106207 m n). Qed.
Lemma lem106209 (m : nat) (n : nat) : (term19 m n) = ((term20 m n) = (term21 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem106228 (P : nat -> Prop) : term22 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem106229 : term23.
Proof. exact (@lem106228 term24). Qed.
Lemma lem106230 : term25 = term26.
Proof. exact (eq_refl term25). Qed.
Lemma lem106231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106232 : term27 = term28.
Proof. exact (MK_COMB (@lem106231) (@lem106230)). Qed.
Lemma lem106233 (n : nat) : (term29 n) = (term30 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem106234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem106235 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem106234) (@lem106233 n)). Qed.
Lemma lem106236 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem106237 (n : nat) : (term35 n) = (term36 n).
Proof. exact (MK_COMB (@lem106235 n) (@lem106236 n)). Qed.
Lemma lem106238 : term37 = term38.
Proof. exact (fun_ext (fun n : nat => @lem106237 n)). Qed.
Lemma lem106239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106240 : term39 = term40.
Proof. exact (MK_COMB (@lem106239) (@lem106238)). Qed.
Lemma lem106241 : term41 = term42.
Proof. exact (MK_COMB (@lem106232) (@lem106240)). Qed.
Lemma lem106242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem106243 : term43 = term44.
Proof. exact (MK_COMB (@lem106242) (@lem106241)). Qed.
Lemma lem106244 (n : nat) : (term29 n) = (term30 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem106245 : term45 = term24.
Proof. exact (fun_ext (fun n : nat => @lem106244 n)). Qed.
Lemma lem106246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106247 : term46 = term47.
Proof. exact (MK_COMB (@lem106246) (@lem106245)). Qed.
Lemma lem106248 : term23 = term48.
Proof. exact (MK_COMB (@lem106243) (@lem106247)). Qed.
Lemma lem106249 : term48.
Proof. exact (EQ_MP (@lem106248) (@lem106229)). Qed.
Lemma lem106252 (n : nat) : (term5 n) = True.
Proof. exact (EQ_MP (@lem106191 n) (@lem106190 n)). Qed.
Lemma lem106253 : term26 = True.
Proof. exact (@lem106252 term49). Qed.
Lemma lem106254 : True = term26.
Proof. exact (SYM (@lem106253)). Qed.
Lemma lem106255 : term26.
Proof. exact (EQ_MP (@lem106254) (@lem0)). Qed.
Lemma lem106257 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (EQ_MP (@lem106209 m n) (@lem106208 m n)). Qed.
Lemma lem106258 (n : nat) : (term50 n) = (term51 n).
Proof. exact (@lem106257 n (S n)). Qed.
Lemma lem106260 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (EQ_MP (@lem106202 m n) (@lem106201 m n)). Qed.
Lemma lem106261 (n : nat) : (term52 n) = (term53 n).
Proof. exact (@lem106260 n n). Qed.
Lemma lem106262 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem106263 (n : nat) : (term54 n) = (term55 n).
Proof. exact (MK_COMB (@lem106262) (@lem106261 n)). Qed.
Lemma lem106264 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem106265 (n : nat) : (term51 n) = (term56 n).
Proof. exact (MK_COMB (@lem106263 n) (@lem106264 n)). Qed.
Lemma lem106266 (n : nat) : (term50 n) = (term56 n).
Proof. exact (TRANS (@lem106258 n) (@lem106265 n)). Qed.
Lemma lem106267 (n : nat) : (term57 n) = (term57 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem106268 (n : nat) : (term34 n) = (term58 n).
Proof. exact (MK_COMB (@lem106267 n) (@lem106266 n)). Qed.
Lemma lem106270 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem106186 m n) (@lem106185 m n)). Qed.
Lemma lem106271 (n : nat) : (term58 n) = True.
Proof. exact (@lem106270 (term53 n) (S n)). Qed.
Lemma lem106272 (n : nat) : (term34 n) = True.
Proof. exact (TRANS (@lem106268 n) (@lem106271 n)). Qed.
Lemma lem106273 (n : nat) : True = (term34 n).
Proof. exact (SYM (@lem106272 n)). Qed.
Lemma lem106274 (n : nat) : term34 n.
Proof. exact (EQ_MP (@lem106273 n) (@lem0)). Qed.
Lemma lem106275 (n : nat) : term36 n.
Proof. exact (fun h0 : term30 n => @lem106274 n). Qed.
Lemma lem106280 : term40.
Proof. exact (fun n : nat => @lem106275 n). Qed.
Lemma lem106281 : term42.
Proof. exact (conj (@lem106255) (@lem106280)). Qed.
Lemma lem106282 : term47.
Proof. exact (@lem106249 (@lem106281)). Qed.
