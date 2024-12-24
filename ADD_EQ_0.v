Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_EQ_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem79121 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem79122 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem79123 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem79122 n) (@lem79121 n)). Qed.
Lemma lem79124 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem79137 : term3.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem79138 : term4.
Proof. exact (proj2 (@lem79137)). Qed.
Lemma lem79139 : term5.
Proof. exact (proj2 (@lem79138)). Qed.
Lemma lem79140 (m : nat) : term6 m.
Proof. exact (@lem79139 m). Qed.
Lemma lem79141 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem79142 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem79141 m) (@lem79140 m)). Qed.
Lemma lem79143 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem79142 m n). Qed.
Lemma lem79144 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem79146 : term11.
Proof. exact (proj1 (@lem79138)). Qed.
Lemma lem79147 (m : nat) : term12 m.
Proof. exact (@lem79146 m). Qed.
Lemma lem79148 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem79149 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem79148 m) (@lem79147 m)). Qed.
Lemma lem79150 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem79149 m n). Qed.
Lemma lem79151 (m : nat) (n : nat) : (term14 m n) = ((term15 m n) = (term10 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem79153 : term16.
Proof. exact (proj1 (@lem79137)). Qed.
Lemma lem79154 (m : nat) : term17 m.
Proof. exact (@lem79153 m). Qed.
Lemma lem79155 (m : nat) : (term17 m) = ((term18 m) = m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem79157 : term19.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem79158 (n : nat) : term20 n.
Proof. exact (@lem79157 n). Qed.
Lemma lem79159 (n : nat) : (term20 n) = ((term21 n) = n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem79162 (P : nat -> Prop) : term22 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem79163 : term23.
Proof. exact (@lem79162 term24). Qed.
Lemma lem79164 : term25 = term26.
Proof. exact (eq_refl term25). Qed.
Lemma lem79165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79166 : term27 = term28.
Proof. exact (MK_COMB (@lem79165) (@lem79164)). Qed.
Lemma lem79167 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem79168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79169 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem79168) (@lem79167 m)). Qed.
Lemma lem79170 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem79171 (m : nat) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem79169 m) (@lem79170 m)). Qed.
Lemma lem79172 : term37 = term38.
Proof. exact (fun_ext (fun m : nat => @lem79171 m)). Qed.
Lemma lem79173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79174 : term39 = term40.
Proof. exact (MK_COMB (@lem79173) (@lem79172)). Qed.
Lemma lem79175 : term41 = term42.
Proof. exact (MK_COMB (@lem79166) (@lem79174)). Qed.
Lemma lem79176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79177 : term43 = term44.
Proof. exact (MK_COMB (@lem79176) (@lem79175)). Qed.
Lemma lem79178 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem79179 : term45 = term24.
Proof. exact (fun_ext (fun m : nat => @lem79178 m)). Qed.
Lemma lem79180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79181 : term46 = term47.
Proof. exact (MK_COMB (@lem79180) (@lem79179)). Qed.
Lemma lem79182 : term23 = term48.
Proof. exact (MK_COMB (@lem79177) (@lem79181)). Qed.
Lemma lem79183 : term48.
Proof. exact (EQ_MP (@lem79182) (@lem79163)). Qed.
Lemma lem79186 (P : nat -> Prop) : term22 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem79187 : term49.
Proof. exact (@lem79186 term50). Qed.
Lemma lem79188 : term51 = ((term52 = (NUMERAL 0)) = term53).
Proof. exact (eq_refl term51). Qed.
Lemma lem79189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79190 : term54 = term55.
Proof. exact (MK_COMB (@lem79189) (@lem79188)). Qed.
Lemma lem79191 (n : nat) : (term56 n) = (((term21 n) = (NUMERAL 0)) = (term57 n)).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem79192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79193 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem79192) (@lem79191 n)). Qed.
Lemma lem79194 (n : nat) : (term60 n) = (((term61 n) = (NUMERAL 0)) = (term62 n)).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem79195 (n : nat) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem79193 n) (@lem79194 n)). Qed.
Lemma lem79196 : term65 = term66.
Proof. exact (fun_ext (fun n : nat => @lem79195 n)). Qed.
Lemma lem79197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79198 : term67 = term68.
Proof. exact (MK_COMB (@lem79197) (@lem79196)). Qed.
Lemma lem79199 : term69 = term70.
Proof. exact (MK_COMB (@lem79190) (@lem79198)). Qed.
Lemma lem79200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79201 : term71 = term72.
Proof. exact (MK_COMB (@lem79200) (@lem79199)). Qed.
Lemma lem79202 (n : nat) : (term56 n) = (((term21 n) = (NUMERAL 0)) = (term57 n)).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem79203 : term73 = term50.
Proof. exact (fun_ext (fun n : nat => @lem79202 n)). Qed.
Lemma lem79204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79205 : term74 = term26.
Proof. exact (MK_COMB (@lem79204) (@lem79203)). Qed.
Lemma lem79206 : term49 = term75.
Proof. exact (MK_COMB (@lem79201) (@lem79205)). Qed.
Lemma lem79207 : term75.
Proof. exact (EQ_MP (@lem79206) (@lem79187)). Qed.
Lemma lem79214 (P : nat -> Prop) : term22 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem79215 (m : nat) : term76 m.
Proof. exact (@lem79214 (term77 m)). Qed.
Lemma lem79216 (m : nat) : (term78 m) = (((term79 m) = (NUMERAL 0)) = (term80 m)).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem79217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79218 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem79217) (@lem79216 m)). Qed.
Lemma lem79219 (m : nat) (n : nat) : (term83 m n) = (((term15 m n) = (NUMERAL 0)) = (term84 m n)).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem79220 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79221 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem79220) (@lem79219 m n)). Qed.
Lemma lem79222 (m : nat) (n : nat) : (term87 m n) = (((term88 m n) = (NUMERAL 0)) = (term89 m n)).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem79223 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem79221 m n) (@lem79222 m n)). Qed.
Lemma lem79224 (m : nat) : (term92 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem79223 m n)). Qed.
Lemma lem79225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79226 (m : nat) : (term94 m) = (term95 m).
Proof. exact (MK_COMB (@lem79225) (@lem79224 m)). Qed.
Lemma lem79227 (m : nat) : (term96 m) = (term97 m).
Proof. exact (MK_COMB (@lem79218 m) (@lem79226 m)). Qed.
Lemma lem79228 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79229 (m : nat) : (term98 m) = (term99 m).
Proof. exact (MK_COMB (@lem79228) (@lem79227 m)). Qed.
Lemma lem79230 (m : nat) (n : nat) : (term83 m n) = (((term15 m n) = (NUMERAL 0)) = (term84 m n)).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem79231 (m : nat) : (term100 m) = (term77 m).
Proof. exact (fun_ext (fun n : nat => @lem79230 m n)). Qed.
Lemma lem79232 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79233 (m : nat) : (term101 m) = (term34 m).
Proof. exact (MK_COMB (@lem79232) (@lem79231 m)). Qed.
Lemma lem79234 (m : nat) : (term76 m) = (term102 m).
Proof. exact (MK_COMB (@lem79229 m) (@lem79233 m)). Qed.
Lemma lem79235 (m : nat) : term102 m.
Proof. exact (EQ_MP (@lem79234 m) (@lem79215 m)). Qed.
Lemma lem79246 (n : nat) : (term21 n) = n.
Proof. exact (EQ_MP (@lem79159 n) (@lem79158 n)). Qed.
Lemma lem79247 : term52 = (NUMERAL 0).
Proof. exact (@lem79246 (NUMERAL 0)). Qed.
Lemma lem79248 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79249 : term103 = term104.
Proof. exact (MK_COMB (@lem79248) (@lem79247)). Qed.
Lemma lem79250 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem79251 : (term52 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem79249) (@lem79250)). Qed.
Lemma lem79253 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79254 (x : nat) : (x = x) = True.
Proof. exact (@lem79253 nat x). Qed.
Lemma lem79255 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem79254 (NUMERAL 0)). Qed.
Lemma lem79256 : (term52 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem79251) (@lem79255)). Qed.
Lemma lem79257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79258 : term105 = (@eq Prop True).
Proof. exact (MK_COMB (@lem79257) (@lem79256)). Qed.
Lemma lem79260 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem79261 : term53 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem79260 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem79263 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79264 (x : nat) : (x = x) = True.
Proof. exact (@lem79263 nat x). Qed.
Lemma lem79265 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem79264 (NUMERAL 0)). Qed.
Lemma lem79266 : term53 = True.
Proof. exact (TRANS (@lem79261) (@lem79265)). Qed.
Lemma lem79267 : ((term52 = (NUMERAL 0)) = term53) = (True = True).
Proof. exact (MK_COMB (@lem79258) (@lem79266)). Qed.
Lemma lem79269 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem79270 : (True = True) = True.
Proof. exact (@lem79269 True). Qed.
Lemma lem79271 : ((term52 = (NUMERAL 0)) = term53) = True.
Proof. exact (TRANS (@lem79267) (@lem79270)). Qed.
Lemma lem79272 : True = ((term52 = (NUMERAL 0)) = term53).
Proof. exact (SYM (@lem79271)). Qed.
Lemma lem79273 : (term52 = (NUMERAL 0)) = term53.
Proof. exact (EQ_MP (@lem79272) (@lem0)). Qed.
Lemma lem79279 (n : nat) : (term21 n) = n.
Proof. exact (EQ_MP (@lem79159 n) (@lem79158 n)). Qed.
Lemma lem79280 (n : nat) : (term61 n) = (S n).
Proof. exact (@lem79279 (S n)). Qed.
Lemma lem79281 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79282 (n : nat) : (term106 n) = (term107 n).
Proof. exact (MK_COMB (@lem79281) (@lem79280 n)). Qed.
Lemma lem79283 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem79284 (n : nat) : ((term61 n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem79282 n) (@lem79283)). Qed.
Lemma lem79286 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79287 (n : nat) : ((term61 n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem79284 n) (@lem79286 n)). Qed.
Lemma lem79288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79289 (n : nat) : (term108 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem79288) (@lem79287 n)). Qed.
Lemma lem79293 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79294 (x : nat) : (x = x) = True.
Proof. exact (@lem79293 nat x). Qed.
Lemma lem79295 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem79294 (NUMERAL 0)). Qed.
Lemma lem79296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79297 : term109 = (and True).
Proof. exact (MK_COMB (@lem79296) (@lem79295)). Qed.
Lemma lem79299 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79300 (n : nat) : (term62 n) = (True /\ False).
Proof. exact (MK_COMB (@lem79297) (@lem79299 n)). Qed.
Lemma lem79302 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem79303 : (True /\ False) = False.
Proof. exact (@lem79302 False). Qed.
Lemma lem79304 (n : nat) : (term62 n) = False.
Proof. exact (TRANS (@lem79300 n) (@lem79303)). Qed.
Lemma lem79305 (n : nat) : (((term61 n) = (NUMERAL 0)) = (term62 n)) = (False = False).
Proof. exact (MK_COMB (@lem79289 n) (@lem79304 n)). Qed.
Lemma lem79307 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem79308 : (False = False) = (~ False).
Proof. exact (@lem79307 False). Qed.
Lemma lem79310 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem79311 : (False = False) = True.
Proof. exact (TRANS (@lem79308) (@lem79310)). Qed.
Lemma lem79312 (n : nat) : (((term61 n) = (NUMERAL 0)) = (term62 n)) = True.
Proof. exact (TRANS (@lem79305 n) (@lem79311)). Qed.
Lemma lem79313 (n : nat) : True = (((term61 n) = (NUMERAL 0)) = (term62 n)).
Proof. exact (SYM (@lem79312 n)). Qed.
Lemma lem79314 (n : nat) : ((term61 n) = (NUMERAL 0)) = (term62 n).
Proof. exact (EQ_MP (@lem79313 n) (@lem0)). Qed.
Lemma lem79320 (m : nat) (n : nat) : (term15 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem79151 m n) (@lem79150 m n)). Qed.
Lemma lem79321 (m : nat) : (term79 m) = (term110 m).
Proof. exact (@lem79320 m (NUMERAL 0)). Qed.
Lemma lem79323 (m : nat) : (term18 m) = m.
Proof. exact (EQ_MP (@lem79155 m) (@lem79154 m)). Qed.
Lemma lem79324 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem79325 (m : nat) : (term110 m) = (S m).
Proof. exact (MK_COMB (@lem79324) (@lem79323 m)). Qed.
Lemma lem79326 (m : nat) : (term79 m) = (S m).
Proof. exact (TRANS (@lem79321 m) (@lem79325 m)). Qed.
Lemma lem79327 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79328 (m : nat) : (term111 m) = (term107 m).
Proof. exact (MK_COMB (@lem79327) (@lem79326 m)). Qed.
Lemma lem79329 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem79330 (m : nat) : ((term79 m) = (NUMERAL 0)) = ((S m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem79328 m) (@lem79329)). Qed.
Lemma lem79332 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79333 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem79332 m). Qed.
Lemma lem79334 (m : nat) : ((term79 m) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem79330 m) (@lem79333 m)). Qed.
Lemma lem79335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79336 (m : nat) : (term112 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem79335) (@lem79334 m)). Qed.
Lemma lem79340 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79341 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem79340 m). Qed.
Lemma lem79342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79343 (m : nat) : (term113 m) = (and False).
Proof. exact (MK_COMB (@lem79342) (@lem79341 m)). Qed.
Lemma lem79345 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79346 (x : nat) : (x = x) = True.
Proof. exact (@lem79345 nat x). Qed.
Lemma lem79347 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem79346 (NUMERAL 0)). Qed.
Lemma lem79348 (m : nat) : (term80 m) = (False /\ True).
Proof. exact (MK_COMB (@lem79343 m) (@lem79347)). Qed.
Lemma lem79350 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem79351 : (False /\ True) = False.
Proof. exact (@lem79350 True). Qed.
Lemma lem79352 (m : nat) : (term80 m) = False.
Proof. exact (TRANS (@lem79348 m) (@lem79351)). Qed.
Lemma lem79353 (m : nat) : (((term79 m) = (NUMERAL 0)) = (term80 m)) = (False = False).
Proof. exact (MK_COMB (@lem79336 m) (@lem79352 m)). Qed.
Lemma lem79355 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem79356 : (False = False) = (~ False).
Proof. exact (@lem79355 False). Qed.
Lemma lem79358 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem79359 : (False = False) = True.
Proof. exact (TRANS (@lem79356) (@lem79358)). Qed.
Lemma lem79360 (m : nat) : (((term79 m) = (NUMERAL 0)) = (term80 m)) = True.
Proof. exact (TRANS (@lem79353 m) (@lem79359)). Qed.
Lemma lem79361 (m : nat) : True = (((term79 m) = (NUMERAL 0)) = (term80 m)).
Proof. exact (SYM (@lem79360 m)). Qed.
Lemma lem79362 (m : nat) : ((term79 m) = (NUMERAL 0)) = (term80 m).
Proof. exact (EQ_MP (@lem79361 m) (@lem0)). Qed.
Lemma lem79368 (m : nat) (n : nat) : (term15 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem79151 m n) (@lem79150 m n)). Qed.
Lemma lem79369 (m : nat) (n : nat) : (term88 m n) = (term114 m n).
Proof. exact (@lem79368 m (S n)). Qed.
Lemma lem79371 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem79144 m n) (@lem79143 m n)). Qed.
Lemma lem79372 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem79373 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (MK_COMB (@lem79372) (@lem79371 m n)). Qed.
Lemma lem79374 (m : nat) (n : nat) : (term88 m n) = (term115 m n).
Proof. exact (TRANS (@lem79369 m n) (@lem79373 m n)). Qed.
Lemma lem79375 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79376 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (MK_COMB (@lem79375) (@lem79374 m n)). Qed.
Lemma lem79377 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem79378 (m : nat) (n : nat) : ((term88 m n) = (NUMERAL 0)) = ((term115 m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem79376 m n) (@lem79377)). Qed.
Lemma lem79380 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79381 (m : nat) (n : nat) : ((term115 m n) = (NUMERAL 0)) = False.
Proof. exact (@lem79380 (term10 m n)). Qed.
Lemma lem79382 (m : nat) (n : nat) : ((term88 m n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem79378 m n) (@lem79381 m n)). Qed.
Lemma lem79383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79384 (m : nat) (n : nat) : (term118 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem79383) (@lem79382 m n)). Qed.
Lemma lem79388 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79389 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem79388 m). Qed.
Lemma lem79390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79391 (m : nat) : (term113 m) = (and False).
Proof. exact (MK_COMB (@lem79390) (@lem79389 m)). Qed.
Lemma lem79393 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem79124 n (@lem79123 n)). Qed.
Lemma lem79394 (m : nat) (n : nat) : (term89 m n) = (False /\ False).
Proof. exact (MK_COMB (@lem79391 m) (@lem79393 n)). Qed.
Lemma lem79396 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem79397 : (False /\ False) = False.
Proof. exact (@lem79396 False). Qed.
Lemma lem79398 (m : nat) (n : nat) : (term89 m n) = False.
Proof. exact (TRANS (@lem79394 m n) (@lem79397)). Qed.
Lemma lem79399 (m : nat) (n : nat) : (((term88 m n) = (NUMERAL 0)) = (term89 m n)) = (False = False).
Proof. exact (MK_COMB (@lem79384 m n) (@lem79398 m n)). Qed.
Lemma lem79401 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem79402 : (False = False) = (~ False).
Proof. exact (@lem79401 False). Qed.
Lemma lem79404 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem79405 : (False = False) = True.
Proof. exact (TRANS (@lem79402) (@lem79404)). Qed.
Lemma lem79406 (m : nat) (n : nat) : (((term88 m n) = (NUMERAL 0)) = (term89 m n)) = True.
Proof. exact (TRANS (@lem79399 m n) (@lem79405)). Qed.
Lemma lem79407 (m : nat) (n : nat) : True = (((term88 m n) = (NUMERAL 0)) = (term89 m n)).
Proof. exact (SYM (@lem79406 m n)). Qed.
Lemma lem79408 (m : nat) (n : nat) : ((term88 m n) = (NUMERAL 0)) = (term89 m n).
Proof. exact (EQ_MP (@lem79407 m n) (@lem0)). Qed.
Lemma lem79409 (m : nat) (n : nat) : term91 m n.
Proof. exact (fun h0 : ((term15 m n) = (NUMERAL 0)) = (term84 m n) => @lem79408 m n). Qed.
Lemma lem79414 (m : nat) : term95 m.
Proof. exact (fun n : nat => @lem79409 m n). Qed.
Lemma lem79415 (m : nat) : term97 m.
Proof. exact (conj (@lem79362 m) (@lem79414 m)). Qed.
Lemma lem79416 (m : nat) : term34 m.
Proof. exact (@lem79235 m (@lem79415 m)). Qed.
Lemma lem79417 (n : nat) : term64 n.
Proof. exact (fun h0 : ((term21 n) = (NUMERAL 0)) = (term57 n) => @lem79314 n). Qed.
Lemma lem79422 : term68.
Proof. exact (fun n : nat => @lem79417 n). Qed.
Lemma lem79423 : term70.
Proof. exact (conj (@lem79273) (@lem79422)). Qed.
Lemma lem79424 : term26.
Proof. exact (@lem79207 (@lem79423)). Qed.
Lemma lem79425 (m : nat) : term36 m.
Proof. exact (fun h0 : term30 m => @lem79416 m). Qed.
Lemma lem79430 : term40.
Proof. exact (fun m : nat => @lem79425 m). Qed.
Lemma lem79431 : term42.
Proof. exact (conj (@lem79424) (@lem79430)). Qed.
Lemma lem79432 : term47.
Proof. exact (@lem79183 (@lem79431)). Qed.
