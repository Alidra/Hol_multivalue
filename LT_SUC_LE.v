Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_SUC_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1834_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem91152 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem91153 (m : nat) : term1 m.
Proof. exact (@lem91152 m). Qed.
Lemma lem91154 (m : nat) : (term1 m) = ((term2 m) = False).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem91156 : term3.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem91157 (m : nat) : term4 m.
Proof. exact (@lem91156 m). Qed.
Lemma lem91158 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem91159 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem91158 m) (@lem91157 m)). Qed.
Lemma lem91160 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem91159 m n). Qed.
Lemma lem91161 (m : nat) (n : nat) : (term6 m n) = ((term7 m n) = (term8 m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem91163 : term9.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem91164 (m : nat) : term10 m.
Proof. exact (@lem91163 m). Qed.
Lemma lem91165 (m : nat) : (term10 m) = ((term11 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem91167 : term12.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem91168 (m : nat) : term13 m.
Proof. exact (@lem91167 m). Qed.
Lemma lem91169 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem91170 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem91169 m) (@lem91168 m)). Qed.
Lemma lem91171 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem91170 m n). Qed.
Lemma lem91172 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (term17 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem91179 (P : nat -> Prop) : term18 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem91180 (m : nat) : term19 m.
Proof. exact (@lem91179 (term20 m)). Qed.
Lemma lem91181 (m : nat) : (term21 m) = ((term22 m) = (term11 m)).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem91182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem91183 (m : nat) : (term23 m) = (term24 m).
Proof. exact (MK_COMB (@lem91182) (@lem91181 m)). Qed.
Lemma lem91184 (m : nat) (n : nat) : (term25 m n) = ((term16 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem91185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91186 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem91185) (@lem91184 m n)). Qed.
Lemma lem91187 (m : nat) (n : nat) : (term28 m n) = ((term29 m n) = (term7 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem91188 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem91186 m n) (@lem91187 m n)). Qed.
Lemma lem91189 (m : nat) : (term32 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem91188 m n)). Qed.
Lemma lem91190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91191 (m : nat) : (term34 m) = (term35 m).
Proof. exact (MK_COMB (@lem91190) (@lem91189 m)). Qed.
Lemma lem91192 (m : nat) : (term36 m) = (term37 m).
Proof. exact (MK_COMB (@lem91183 m) (@lem91191 m)). Qed.
Lemma lem91193 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91194 (m : nat) : (term38 m) = (term39 m).
Proof. exact (MK_COMB (@lem91193) (@lem91192 m)). Qed.
Lemma lem91195 (m : nat) (n : nat) : (term25 m n) = ((term16 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem91196 (m : nat) : (term40 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem91195 m n)). Qed.
Lemma lem91197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91198 (m : nat) : (term41 m) = (term42 m).
Proof. exact (MK_COMB (@lem91197) (@lem91196 m)). Qed.
Lemma lem91199 (m : nat) : (term19 m) = (term43 m).
Proof. exact (MK_COMB (@lem91194 m) (@lem91198 m)). Qed.
Lemma lem91200 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem91199 m) (@lem91180 m)). Qed.
Lemma lem91205 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem91172 m n) (@lem91171 m n)). Qed.
Lemma lem91206 (m : nat) : (term22 m) = (term44 m).
Proof. exact (@lem91205 m (NUMERAL 0)). Qed.
Lemma lem91207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91208 (m : nat) : (term45 m) = (term46 m).
Proof. exact (MK_COMB (@lem91207) (@lem91206 m)). Qed.
Lemma lem91210 (m : nat) : (term11 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem91165 m) (@lem91164 m)). Qed.
Lemma lem91211 (m : nat) : ((term22 m) = (term11 m)) = ((term44 m) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem91208 m) (@lem91210 m)). Qed.
Lemma lem91212 (m : nat) : ((term44 m) = (m = (NUMERAL 0))) = ((term22 m) = (term11 m)).
Proof. exact (SYM (@lem91211 m)). Qed.
Lemma lem91216 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem91172 m n) (@lem91171 m n)). Qed.
Lemma lem91217 (m : nat) (n : nat) : (term29 m n) = (term47 m n).
Proof. exact (@lem91216 m (S n)). Qed.
Lemma lem91218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91219 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem91218) (@lem91217 m n)). Qed.
Lemma lem91221 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem91161 m n) (@lem91160 m n)). Qed.
Lemma lem91222 (m : nat) (n : nat) : ((term29 m n) = (term7 m n)) = ((term47 m n) = (term8 m n)).
Proof. exact (MK_COMB (@lem91219 m n) (@lem91221 m n)). Qed.
Lemma lem91223 (m : nat) (n : nat) : ((term47 m n) = (term8 m n)) = ((term29 m n) = (term7 m n)).
Proof. exact (SYM (@lem91222 m n)). Qed.
Lemma lem91241 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : (term16 m n) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem91242 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem91243 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : (term47 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem91242 m n) (@lem91241 m n h1)). Qed.
Lemma lem91246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91247 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : (term49 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem91246) (@lem91243 m n h1)). Qed.
Lemma lem91252 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem91253 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : ((term47 m n) = (term8 m n)) = ((term8 m n) = (term8 m n)).
Proof. exact (MK_COMB (@lem91247 m n h1) (@lem91252 m n)). Qed.
Lemma lem91255 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91256 (x : Prop) : (x = x) = True.
Proof. exact (@lem91255 Prop x). Qed.
Lemma lem91257 (m : nat) (n : nat) : ((term8 m n) = (term8 m n)) = True.
Proof. exact (@lem91256 (term8 m n)). Qed.
Lemma lem91258 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : ((term47 m n) = (term8 m n)) = True.
Proof. exact (TRANS (@lem91253 m n h1) (@lem91257 m n)). Qed.
Lemma lem91259 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : True = ((term47 m n) = (term8 m n)).
Proof. exact (SYM (@lem91258 m n h1)). Qed.
Lemma lem91260 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : (term47 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem91259 m n h1) (@lem0)). Qed.
Lemma lem91268 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem91154 m) (@lem91153 m)). Qed.
Lemma lem91269 (m : nat) : (term52 m) = (term52 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem91270 (m : nat) : (term44 m) = (term53 m).
Proof. exact (MK_COMB (@lem91269 m) (@lem91268 m)). Qed.
Lemma lem91272 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem91273 (m : nat) : (term53 m) = (m = (NUMERAL 0)).
Proof. exact (@lem91272 (m = (NUMERAL 0))). Qed.
Lemma lem91276 (m : nat) : (term44 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem91270 m) (@lem91273 m)). Qed.
Lemma lem91277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91278 (m : nat) : (term46 m) = (term54 m).
Proof. exact (MK_COMB (@lem91277) (@lem91276 m)). Qed.
Lemma lem91281 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem91282 (m : nat) : ((term44 m) = (m = (NUMERAL 0))) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem91278 m) (@lem91281 m)). Qed.
Lemma lem91284 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91285 (x : Prop) : (x = x) = True.
Proof. exact (@lem91284 Prop x). Qed.
Lemma lem91286 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem91285 (m = (NUMERAL 0))). Qed.
Lemma lem91287 (m : nat) : ((term44 m) = (m = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem91282 m) (@lem91286 m)). Qed.
Lemma lem91288 (m : nat) : True = ((term44 m) = (m = (NUMERAL 0))).
Proof. exact (SYM (@lem91287 m)). Qed.
Lemma lem91290 (m : nat) : (term44 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem91288 m) (@lem0)). Qed.
Lemma lem91291 (m : nat) (n : nat) (h1 : (term16 m n) = (Peano.le m n)) : (term29 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem91223 m n) (@lem91260 m n h1)). Qed.
Lemma lem91292 (m : nat) : (term22 m) = (term11 m).
Proof. exact (EQ_MP (@lem91212 m) (@lem91290 m)). Qed.
Lemma lem91293 (m : nat) (n : nat) : term31 m n.
Proof. exact (fun h0 : (term16 m n) = (Peano.le m n) => @lem91291 m n h0). Qed.
Lemma lem91298 (m : nat) : term35 m.
Proof. exact (fun n : nat => @lem91293 m n). Qed.
Lemma lem91299 (m : nat) : term37 m.
Proof. exact (conj (@lem91292 m) (@lem91298 m)). Qed.
Lemma lem91300 (m : nat) : term42 m.
Proof. exact (@lem91200 m (@lem91299 m)). Qed.
Lemma lem91305 : term55.
Proof. exact (fun m : nat => @lem91300 m). Qed.
