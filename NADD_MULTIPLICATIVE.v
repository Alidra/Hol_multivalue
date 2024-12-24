Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MULTIPLICATIVE_term_abbrevs.
Require Import ADD_AC_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DIST_LMUL_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXISTS_REFL_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_EXISTS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import MULT_AC_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NADD_CAUCHY_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1247221_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1263163 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem1263164 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem1263163 A x a h1)). Qed.
Lemma lem1263165 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem1263166 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem1263165 A a x h1)). Qed.
Lemma lem1263167 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem1263164 A x a h1) (fun h1 : a = x => @lem1263166 A a x h1)). Qed.
Lemma lem1263168 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem1263167 A a x)). Qed.
Lemma lem1263169 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1263170 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem1263169 A) (@lem1263168 A a)). Qed.
Lemma lem1263171 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem1263170 A a)). Qed.
Lemma lem1263172 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1263173 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem1263172 A) (@lem1263171 A)). Qed.
Lemma lem1263174 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem1263173 A) (@lem4363 A)). Qed.
Lemma lem1263175 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem1263174 A a). Qed.
Lemma lem1263176 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem1263177 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem1263176 A a) (@lem1263175 A a)). Qed.
Lemma lem1263178 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem1263180 (n : nat) (m : nat) (p : nat) : term9 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1263184 (m : nat) : term10 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1263185 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1263186 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1263185 m) (@lem1263184 m)). Qed.
Lemma lem1263187 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1263186 m n). Qed.
Lemma lem1263188 (n : nat) (m : nat) : (term12 m n) = (term13 n m).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1263189 (n : nat) (m : nat) : term13 n m.
Proof. exact (EQ_MP (@lem1263188 n m) (@lem1263187 m n)). Qed.
Lemma lem1263190 (n : nat) (m : nat) (p : nat) : term14 n m p.
Proof. exact (@lem1263189 n m p). Qed.
Lemma lem1263191 (n : nat) (m : nat) (p : nat) : (term14 n m p) = ((term15 m n p) = (term16 n m p)).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem1263193 (m : nat) : term17 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1263194 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1263195 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1263194 m) (@lem1263193 m)). Qed.
Lemma lem1263196 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1263195 m n). Qed.
Lemma lem1263197 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1263198 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem1263197 m n) (@lem1263196 m n)). Qed.
Lemma lem1263199 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem1263198 m n p). Qed.
Lemma lem1263200 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term22 m n p) = (term23 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem1263202 (m : nat) : term24 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1263203 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1263204 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1263203 m) (@lem1263202 m)). Qed.
Lemma lem1263205 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1263204 m n). Qed.
Lemma lem1263206 (n : nat) (m : nat) : (term26 m n) = ((Peano.le m n) = (term27 n m)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1263208 (m : nat) : term28 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1263209 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1263210 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1263209 m) (@lem1263208 m)). Qed.
Lemma lem1263211 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1263210 m n). Qed.
Lemma lem1263212 (n : nat) (m : nat) : (term30 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1263214 (m : nat) : term31 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem1263215 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1263216 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1263215 m) (@lem1263214 m)). Qed.
Lemma lem1263217 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1263216 m n). Qed.
Lemma lem1263218 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1263219 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem1263218 m n) (@lem1263217 m n)). Qed.
Lemma lem1263220 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (@lem1263219 m n p). Qed.
Lemma lem1263221 (m : nat) (n : nat) (p : nat) : (term35 m n p) = ((term36 m n p) = (term37 m n p)).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem1263226 (m : nat) (n : nat) (p : nat) (h1 : (term38 n m p) = (term39 m n p)) : (term38 n m p) = (term39 m n p).
Proof. exact (h1). Qed.
Lemma lem1263227 (m : nat) (n : nat) (p : nat) (h1 : (term38 n m p) = (term39 m n p)) : (term39 m n p) = (term38 n m p).
Proof. exact (SYM (@lem1263226 m n p h1)). Qed.
Lemma lem1263228 (n : nat) (m : nat) (p : nat) (h1 : (term39 m n p) = (term38 n m p)) : (term39 m n p) = (term38 n m p).
Proof. exact (h1). Qed.
Lemma lem1263229 (n : nat) (m : nat) (p : nat) (h1 : (term39 m n p) = (term38 n m p)) : (term38 n m p) = (term39 m n p).
Proof. exact (SYM (@lem1263228 n m p h1)). Qed.
Lemma lem1263230 (n : nat) (m : nat) (p : nat) : ((term38 n m p) = (term39 m n p)) = ((term39 m n p) = (term38 n m p)).
Proof. exact (prop_ext (fun h1 : (term38 n m p) = (term39 m n p) => @lem1263227 m n p h1) (fun h1 : (term39 m n p) = (term38 n m p) => @lem1263229 n m p h1)). Qed.
Lemma lem1263231 (n : nat) (m : nat) : (term40 m n) = (term41 n m).
Proof. exact (fun_ext (fun p : nat => @lem1263230 n m p)). Qed.
Lemma lem1263232 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1263233 (n : nat) (m : nat) : (term42 m n) = (term43 n m).
Proof. exact (MK_COMB (@lem1263232) (@lem1263231 n m)). Qed.
Lemma lem1263234 (m : nat) : (term44 m) = (term45 m).
Proof. exact (fun_ext (fun n : nat => @lem1263233 n m)). Qed.
Lemma lem1263235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1263236 (m : nat) : (term46 m) = (term47 m).
Proof. exact (MK_COMB (@lem1263235) (@lem1263234 m)). Qed.
Lemma lem1263237 : term48 = term49.
Proof. exact (fun_ext (fun m : nat => @lem1263236 m)). Qed.
Lemma lem1263238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1263239 : term50 = term51.
Proof. exact (MK_COMB (@lem1263238) (@lem1263237)). Qed.
Lemma lem1263240 : term51.
Proof. exact (EQ_MP (@lem1263239) (@lem104208)). Qed.
Lemma lem1263249 (a : Prop) : term52 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem1263250 (a : Prop) : (term52 a) = (term53 a).
Proof. exact (eq_refl (term52 a)). Qed.
Lemma lem1263251 (a : Prop) : term53 a.
Proof. exact (EQ_MP (@lem1263250 a) (@lem1263249 a)). Qed.
Lemma lem1263252 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem1263253 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem1263262 (b : Prop) : (term54 b) = (term54 b).
Proof. exact (eq_refl (term54 b)). Qed.
Lemma lem1263263 (b : Prop) (a : Prop) (h1 : a = True) : (term55 b a) = (term56 b).
Proof. exact (MK_COMB (@lem1263262 b) (@lem1263252 a h1)). Qed.
Lemma lem1263264 (b : Prop) : (term56 b) = ((term57 b) = (True \/ b)).
Proof. exact (eq_refl (term56 b)). Qed.
Lemma lem1263265 (b : Prop) (a : Prop) : (term58 b a) = (term58 b a).
Proof. exact (eq_refl (term58 b a)). Qed.
Lemma lem1263266 (a : Prop) (b : Prop) : ((term55 b a) = (term56 b)) = ((term55 b a) = ((term57 b) = (True \/ b))).
Proof. exact (MK_COMB (@lem1263265 b a) (@lem1263264 b)). Qed.
Lemma lem1263267 (a : Prop) (b : Prop) : (term55 b a) = ((term59 a b) = (a \/ b)).
Proof. exact (eq_refl (term55 b a)). Qed.
Lemma lem1263268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1263269 (a : Prop) (b : Prop) : (term58 b a) = (term60 a b).
Proof. exact (MK_COMB (@lem1263268) (@lem1263267 a b)). Qed.
Lemma lem1263270 (b : Prop) : ((term57 b) = (True \/ b)) = ((term57 b) = (True \/ b)).
Proof. exact (eq_refl ((term57 b) = (True \/ b))). Qed.
Lemma lem1263271 (a : Prop) (b : Prop) : ((term55 b a) = ((term57 b) = (True \/ b))) = (((term59 a b) = (a \/ b)) = ((term57 b) = (True \/ b))).
Proof. exact (MK_COMB (@lem1263269 a b) (@lem1263270 b)). Qed.
Lemma lem1263272 (a : Prop) (b : Prop) : ((term55 b a) = (term56 b)) = (((term59 a b) = (a \/ b)) = ((term57 b) = (True \/ b))).
Proof. exact (TRANS (@lem1263266 a b) (@lem1263271 a b)). Qed.
Lemma lem1263273 (b : Prop) (a : Prop) (h1 : a = True) : ((term59 a b) = (a \/ b)) = ((term57 b) = (True \/ b)).
Proof. exact (EQ_MP (@lem1263272 a b) (@lem1263263 b a h1)). Qed.
Lemma lem1263274 (b : Prop) (a : Prop) (h1 : a = True) : ((term57 b) = (True \/ b)) = ((term59 a b) = (a \/ b)).
Proof. exact (SYM (@lem1263273 b a h1)). Qed.
Lemma lem1263275 (b : Prop) : (term54 b) = (term54 b).
Proof. exact (eq_refl (term54 b)). Qed.
Lemma lem1263276 (b : Prop) (a : Prop) (h1 : a = False) : (term55 b a) = (term61 b).
Proof. exact (MK_COMB (@lem1263275 b) (@lem1263253 a h1)). Qed.
Lemma lem1263277 (b : Prop) : (term61 b) = ((term62 b) = (False \/ b)).
Proof. exact (eq_refl (term61 b)). Qed.
Lemma lem1263278 (b : Prop) (a : Prop) : (term58 b a) = (term58 b a).
Proof. exact (eq_refl (term58 b a)). Qed.
Lemma lem1263279 (a : Prop) (b : Prop) : ((term55 b a) = (term61 b)) = ((term55 b a) = ((term62 b) = (False \/ b))).
Proof. exact (MK_COMB (@lem1263278 b a) (@lem1263277 b)). Qed.
Lemma lem1263280 (a : Prop) (b : Prop) : (term55 b a) = ((term59 a b) = (a \/ b)).
Proof. exact (eq_refl (term55 b a)). Qed.
Lemma lem1263281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1263282 (a : Prop) (b : Prop) : (term58 b a) = (term60 a b).
Proof. exact (MK_COMB (@lem1263281) (@lem1263280 a b)). Qed.
Lemma lem1263283 (b : Prop) : ((term62 b) = (False \/ b)) = ((term62 b) = (False \/ b)).
Proof. exact (eq_refl ((term62 b) = (False \/ b))). Qed.
Lemma lem1263284 (a : Prop) (b : Prop) : ((term55 b a) = ((term62 b) = (False \/ b))) = (((term59 a b) = (a \/ b)) = ((term62 b) = (False \/ b))).
Proof. exact (MK_COMB (@lem1263282 a b) (@lem1263283 b)). Qed.
Lemma lem1263285 (a : Prop) (b : Prop) : ((term55 b a) = (term61 b)) = (((term59 a b) = (a \/ b)) = ((term62 b) = (False \/ b))).
Proof. exact (TRANS (@lem1263279 a b) (@lem1263284 a b)). Qed.
Lemma lem1263286 (b : Prop) (a : Prop) (h1 : a = False) : ((term59 a b) = (a \/ b)) = ((term62 b) = (False \/ b)).
Proof. exact (EQ_MP (@lem1263285 a b) (@lem1263276 b a h1)). Qed.
Lemma lem1263287 (b : Prop) (a : Prop) (h1 : a = False) : ((term62 b) = (False \/ b)) = ((term59 a b) = (a \/ b)).
Proof. exact (SYM (@lem1263286 b a h1)). Qed.
Lemma lem1263293 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1263294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1263295 : term63 = (imp False).
Proof. exact (MK_COMB (@lem1263294) (@lem1263293)). Qed.
Lemma lem1263296 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1263297 (b : Prop) : (term57 b) = (False -> b).
Proof. exact (MK_COMB (@lem1263295) (@lem1263296 b)). Qed.
Lemma lem1263299 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1263300 (b : Prop) : (False -> b) = True.
Proof. exact (@lem1263299 b). Qed.
Lemma lem1263301 (b : Prop) : (term57 b) = True.
Proof. exact (TRANS (@lem1263297 b) (@lem1263300 b)). Qed.
Lemma lem1263302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1263303 (b : Prop) : (term64 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1263302) (@lem1263301 b)). Qed.
Lemma lem1263305 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1263306 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem1263305 b). Qed.
Lemma lem1263307 (b : Prop) : ((term57 b) = (True \/ b)) = (True = True).
Proof. exact (MK_COMB (@lem1263303 b) (@lem1263306 b)). Qed.
Lemma lem1263309 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1263310 : (True = True) = True.
Proof. exact (@lem1263309 True). Qed.
Lemma lem1263311 (b : Prop) : ((term57 b) = (True \/ b)) = True.
Proof. exact (TRANS (@lem1263307 b) (@lem1263310)). Qed.
Lemma lem1263312 (b : Prop) : True = ((term57 b) = (True \/ b)).
Proof. exact (SYM (@lem1263311 b)). Qed.
Lemma lem1263313 (b : Prop) : (term57 b) = (True \/ b).
Proof. exact (EQ_MP (@lem1263312 b) (@lem0)). Qed.
Lemma lem1263319 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1263320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1263321 : term65 = (imp True).
Proof. exact (MK_COMB (@lem1263320) (@lem1263319)). Qed.
Lemma lem1263322 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1263323 (b : Prop) : (term62 b) = (True -> b).
Proof. exact (MK_COMB (@lem1263321) (@lem1263322 b)). Qed.
Lemma lem1263325 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1263326 (b : Prop) : (True -> b) = b.
Proof. exact (@lem1263325 b). Qed.
Lemma lem1263327 (b : Prop) : (term62 b) = b.
Proof. exact (TRANS (@lem1263323 b) (@lem1263326 b)). Qed.
Lemma lem1263328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1263329 (b : Prop) : (term66 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem1263328) (@lem1263327 b)). Qed.
Lemma lem1263331 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1263332 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem1263331 b). Qed.
Lemma lem1263333 (b : Prop) : ((term62 b) = (False \/ b)) = (b = b).
Proof. exact (MK_COMB (@lem1263329 b) (@lem1263332 b)). Qed.
Lemma lem1263335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1263336 (x : Prop) : (x = x) = True.
Proof. exact (@lem1263335 Prop x). Qed.
Lemma lem1263337 (b : Prop) : (b = b) = True.
Proof. exact (@lem1263336 b). Qed.
Lemma lem1263338 (b : Prop) : ((term62 b) = (False \/ b)) = True.
Proof. exact (TRANS (@lem1263333 b) (@lem1263337 b)). Qed.
Lemma lem1263339 (b : Prop) : True = ((term62 b) = (False \/ b)).
Proof. exact (SYM (@lem1263338 b)). Qed.
Lemma lem1263340 (b : Prop) : (term62 b) = (False \/ b).
Proof. exact (EQ_MP (@lem1263339 b) (@lem0)). Qed.
Lemma lem1263341 (b : Prop) (a : Prop) (h1 : a = False) : (term59 a b) = (a \/ b).
Proof. exact (EQ_MP (@lem1263287 b a h1) (@lem1263340 b)). Qed.
Lemma lem1263342 (b : Prop) (a : Prop) (h1 : a = True) : (term59 a b) = (a \/ b).
Proof. exact (EQ_MP (@lem1263274 b a h1) (@lem1263313 b)). Qed.
Lemma lem1263346 (m : nat) : term67 m.
Proof. exact (@lem1245388 m). Qed.
Lemma lem1263347 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem1263348 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem1263347 m) (@lem1263346 m)). Qed.
Lemma lem1263349 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem1263348 m n). Qed.
Lemma lem1263350 (n : nat) (m : nat) : (term69 m n) = (term70 n m).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem1263351 (n : nat) (m : nat) : term70 n m.
Proof. exact (EQ_MP (@lem1263350 n m) (@lem1263349 m n)). Qed.
Lemma lem1263352 (n : nat) (m : nat) (p : nat) : term71 n m p.
Proof. exact (@lem1263351 n m p). Qed.
Lemma lem1263353 (n : nat) (m : nat) (p : nat) : (term71 n m p) = ((term72 m n p) = (term73 n m p)).
Proof. exact (eq_refl (term71 n m p)). Qed.
Lemma lem1263355 (m : nat) : term74 m.
Proof. exact (@lem1263240 m). Qed.
Lemma lem1263356 (m : nat) : (term74 m) = (term47 m).
Proof. exact (eq_refl (term74 m)). Qed.
Lemma lem1263357 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1263356 m) (@lem1263355 m)). Qed.
Lemma lem1263358 (m : nat) (n : nat) : term75 m n.
Proof. exact (@lem1263357 m n). Qed.
Lemma lem1263359 (n : nat) (m : nat) : (term75 m n) = (term43 n m).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem1263360 (n : nat) (m : nat) : term43 n m.
Proof. exact (EQ_MP (@lem1263359 n m) (@lem1263358 m n)). Qed.
Lemma lem1263361 (n : nat) (m : nat) (p : nat) : term76 n m p.
Proof. exact (@lem1263360 n m p). Qed.
Lemma lem1263362 (n : nat) (m : nat) (p : nat) : (term76 n m p) = ((term39 m n p) = (term38 n m p)).
Proof. exact (eq_refl (term76 n m p)). Qed.
Lemma lem1263366 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem1263367 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem1263366 A x a h1)). Qed.
Lemma lem1263368 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem1263369 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem1263368 A a x h1)). Qed.
Lemma lem1263370 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem1263367 A x a h1) (fun h1 : a = x => @lem1263369 A a x h1)). Qed.
Lemma lem1263371 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem1263370 A a x)). Qed.
Lemma lem1263372 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1263373 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem1263372 A) (@lem1263371 A a)). Qed.
Lemma lem1263374 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem1263373 A a)). Qed.
Lemma lem1263375 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1263376 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem1263375 A) (@lem1263374 A)). Qed.
Lemma lem1263377 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem1263376 A) (@lem4363 A)). Qed.
Lemma lem1263378 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem1263377 A a). Qed.
Lemma lem1263379 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem1263380 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem1263379 A a) (@lem1263378 A a)). Qed.
Lemma lem1263381 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem1263383 (m : nat) : term24 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1263384 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1263385 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1263384 m) (@lem1263383 m)). Qed.
Lemma lem1263386 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1263385 m n). Qed.
Lemma lem1263387 (n : nat) (m : nat) : (term26 m n) = ((Peano.le m n) = (term27 n m)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1263389 (m : nat) : term77 m.
Proof. exact (@lem1247221 m). Qed.
Lemma lem1263390 (m : nat) : (term77 m) = (term78 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem1263391 (m : nat) : term78 m.
Proof. exact (EQ_MP (@lem1263390 m) (@lem1263389 m)). Qed.
Lemma lem1263392 (m : nat) (n : nat) : term79 m n.
Proof. exact (@lem1263391 m n). Qed.
Lemma lem1263393 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem1263394 (m : nat) (n : nat) : term80 m n.
Proof. exact (EQ_MP (@lem1263393 m n) (@lem1263392 m n)). Qed.
Lemma lem1263395 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem1263396 (m : nat) (h1 : term81) : term82 m.
Proof. exact (@lem1263395 h1 m). Qed.
Lemma lem1263397 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1263398 (m : nat) (h1 : term81) : term83 m.
Proof. exact (EQ_MP (@lem1263397 m) (@lem1263396 m h1)). Qed.
Lemma lem1263399 (m : nat) (n : nat) (h1 : term81) : term84 m n.
Proof. exact (@lem1263398 m h1 n). Qed.
Lemma lem1263400 (n : nat) (m : nat) : (term84 m n) = (term85 n m).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1263401 (n : nat) (m : nat) (h1 : term81) : term85 n m.
Proof. exact (EQ_MP (@lem1263400 n m) (@lem1263399 m n h1)). Qed.
Lemma lem1263402 (n : nat) (m : nat) (p : nat) (h1 : term81) : term86 n m p.
Proof. exact (@lem1263401 n m h1 p). Qed.
Lemma lem1263403 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term87 n m p).
Proof. exact (eq_refl (term86 n m p)). Qed.
Lemma lem1263404 (n : nat) (m : nat) (p : nat) (h1 : term81) : term87 n m p.
Proof. exact (EQ_MP (@lem1263403 n m p) (@lem1263402 n m p h1)). Qed.
Lemma lem1263405 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1263406 (p : nat) (m : nat) (n : nat) (h1 : term81) (h2 : Peano.le m n) : term88 n m p.
Proof. exact (@lem1263404 n m p h1 (@lem1263405 m n h2)). Qed.
Lemma lem1263407 (m : nat) (n : nat) (h1 : term81) (h2 : Peano.le m n) : term89 n m.
Proof. exact (fun p : nat => @lem1263406 p m n h1 h2). Qed.
Lemma lem1263408 (n : nat) (m : nat) (h1 : term81) : term90 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1263407 m n h1 h0). Qed.
Lemma lem1263409 (m : nat) (h1 : term81) : term91 m.
Proof. exact (fun n : nat => @lem1263408 n m h1). Qed.
Lemma lem1263410 (h1 : term81) : term92.
Proof. exact (fun m : nat => @lem1263409 m h1). Qed.
Lemma lem1263411 : term93.
Proof. exact (fun h0 : term81 => @lem1263410 h0). Qed.
Lemma lem1263412 : term92.
Proof. exact (@lem1263411 (@lem272809)). Qed.
Lemma lem1263413 (m : nat) : term94 m.
Proof. exact (@lem1263412 m). Qed.
Lemma lem1263414 (m : nat) : (term94 m) = (term91 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem1263415 (m : nat) : term91 m.
Proof. exact (EQ_MP (@lem1263414 m) (@lem1263413 m)). Qed.
Lemma lem1263416 (m : nat) (n : nat) : term95 m n.
Proof. exact (@lem1263415 m n). Qed.
Lemma lem1263417 (n : nat) (m : nat) : (term95 m n) = (term90 n m).
Proof. exact (eq_refl (term95 m n)). Qed.
Lemma lem1263420 (n : nat) (m : nat) : term90 n m.
Proof. exact (EQ_MP (@lem1263417 n m) (@lem1263416 m n)). Qed.
Lemma lem1263421 (m : nat) (n : nat) : term96 m n.
Proof. exact (@lem1263420 (Nat.add m n) (term97 m n)). Qed.
Lemma lem1263422 (m : nat) (n : nat) : term98 m n.
Proof. exact (@lem1263421 m n (@lem1263394 m n)). Qed.
Lemma lem1263423 (m : nat) : term99 m.
Proof. exact (fun n : nat => @lem1263422 m n). Qed.
Lemma lem1263424 : term100.
Proof. exact (fun m : nat => @lem1263423 m). Qed.
Lemma lem1263425 (h1 : term100) : term100.
Proof. exact (h1). Qed.
Lemma lem1263426 (m : nat) (h1 : term100) : term101 m.
Proof. exact (@lem1263425 h1 m). Qed.
Lemma lem1263427 (m : nat) : (term101 m) = (term99 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem1263428 (m : nat) (h1 : term100) : term99 m.
Proof. exact (EQ_MP (@lem1263427 m) (@lem1263426 m h1)). Qed.
Lemma lem1263429 (m : nat) (n : nat) (h1 : term100) : term102 m n.
Proof. exact (@lem1263428 m h1 n). Qed.
Lemma lem1263430 (m : nat) (n : nat) : (term102 m n) = (term98 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem1263431 (m : nat) (n : nat) (h1 : term100) : term98 m n.
Proof. exact (EQ_MP (@lem1263430 m n) (@lem1263429 m n h1)). Qed.
Lemma lem1263432 (m : nat) (n : nat) (p : nat) (h1 : term100) : term103 m n p.
Proof. exact (@lem1263431 m n h1 p). Qed.
Lemma lem1263433 (m : nat) (n : nat) (p : nat) : (term103 m n p) = (term104 m n p).
Proof. exact (eq_refl (term103 m n p)). Qed.
Lemma lem1263434 (m : nat) (n : nat) (p : nat) (h1 : term100) : term104 m n p.
Proof. exact (EQ_MP (@lem1263433 m n p) (@lem1263432 m n p h1)). Qed.
Lemma lem1263435 (m : nat) (n : nat) (p : nat) (h1 : term105 m n p) : term105 m n p.
Proof. exact (h1). Qed.
Lemma lem1263436 (m : nat) (n : nat) (p : nat) (h1 : term100) (h2 : term105 m n p) : term106 m n p.
Proof. exact (@lem1263434 m n p h1 (@lem1263435 m n p h2)). Qed.
Lemma lem1263437 (m : nat) (n : nat) (p : nat) (h1 : term105 m n p) : term107 m n p.
Proof. exact (fun h0 : term100 => @lem1263436 m n p h0 h1). Qed.
Lemma lem1263438 (h1 : term100) : term100.
Proof. exact (h1). Qed.
Lemma lem1263439 (m : nat) (n : nat) (p : nat) (h1 : term100) (h2 : term105 m n p) : term106 m n p.
Proof. exact (@lem1263437 m n p h2 (@lem1263438 h1)). Qed.
Lemma lem1263440 (m : nat) (n : nat) (p : nat) (h1 : term100) : term104 m n p.
Proof. exact (fun h0 : term105 m n p => @lem1263439 m n p h1 h0). Qed.
Lemma lem1263441 (m : nat) (n : nat) (h1 : term100) : term98 m n.
Proof. exact (fun p : nat => @lem1263440 m n p h1). Qed.
Lemma lem1263442 (m : nat) (h1 : term100) : term99 m.
Proof. exact (fun n : nat => @lem1263441 m n h1). Qed.
Lemma lem1263443 (h1 : term100) : term100.
Proof. exact (fun m : nat => @lem1263442 m h1). Qed.
Lemma lem1263444 : term108.
Proof. exact (fun h0 : term100 => @lem1263443 h0). Qed.
Lemma lem1263445 : term100.
Proof. exact (@lem1263444 (@lem1263424)). Qed.
Lemma lem1263446 (m : nat) : term101 m.
Proof. exact (@lem1263445 m). Qed.
Lemma lem1263447 (m : nat) : (term101 m) = (term99 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem1263448 (m : nat) : term99 m.
Proof. exact (EQ_MP (@lem1263447 m) (@lem1263446 m)). Qed.
Lemma lem1263449 (m : nat) (n : nat) : term102 m n.
Proof. exact (@lem1263448 m n). Qed.
Lemma lem1263450 (m : nat) (n : nat) : (term102 m n) = (term98 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem1263451 (m : nat) (n : nat) : term98 m n.
Proof. exact (EQ_MP (@lem1263450 m n) (@lem1263449 m n)). Qed.
Lemma lem1263452 (m : nat) (n : nat) (p : nat) : term103 m n p.
Proof. exact (@lem1263451 m n p). Qed.
Lemma lem1263453 (m : nat) (n : nat) (p : nat) : (term103 m n p) = (term104 m n p).
Proof. exact (eq_refl (term103 m n p)). Qed.
Lemma lem1263455 (n : nat) : term109 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1263456 (n : nat) : (term109 n) = (term110 n).
Proof. exact (eq_refl (term109 n)). Qed.
Lemma lem1263457 (n : nat) : term110 n.
Proof. exact (EQ_MP (@lem1263456 n) (@lem1263455 n)). Qed.
Lemma lem1263459 (n : nat) (h1 : term111 n) : term111 n.
Proof. exact (h1). Qed.
Lemma lem1263460 (x : nadd) : term112 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1263461 (x : nadd) : (term112 x) = (term113 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1263462 (x : nadd) : term113 x.
Proof. exact (EQ_MP (@lem1263461 x) (@lem1263460 x)). Qed.
Lemma lem1263463 (x : nadd) (B : nat) (h1 : term114 x B) : term114 x B.
Proof. exact (h1). Qed.
Lemma lem1263465 (m : nat) (n : nat) (p : nat) : term104 m n p.
Proof. exact (EQ_MP (@lem1263453 m n p) (@lem1263452 m n p)). Qed.
Lemma lem1263466 (n : nat) (m : nat) (B : nat) (x : nadd) : term115 n m B x.
Proof. exact (@lem1263465 (term116 x m n) (term117 m x n) (term118 m B x)). Qed.
Lemma lem1263471 (m : nat) : term17 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1263472 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1263473 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1263472 m) (@lem1263471 m)). Qed.
Lemma lem1263474 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1263473 m n). Qed.
Lemma lem1263475 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1263476 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem1263475 m n) (@lem1263474 m n)). Qed.
Lemma lem1263477 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem1263476 m n p). Qed.
Lemma lem1263478 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term22 m n p) = (term23 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem1263480 : term119.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1263506 : term120.
Proof. exact (proj1 (@lem1263480)). Qed.
Lemma lem1263507 (m : nat) : term121 m.
Proof. exact (@lem1263506 m). Qed.
Lemma lem1263508 (m : nat) : (term121 m) = ((term122 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem1263525 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1263526 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1263527 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul m n) = (term122 m).
Proof. exact (MK_COMB (@lem1263526 m) (@lem1263525 n h1)). Qed.
Lemma lem1263529 (m : nat) : (term122 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1263508 m) (@lem1263507 m)). Qed.
Lemma lem1263530 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1263527 m n h1) (@lem1263529 m)). Qed.
Lemma lem1263531 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1263532 (m : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term116 x m n) = (term123 x).
Proof. exact (MK_COMB (@lem1263531 x) (@lem1263530 m n h1)). Qed.
Lemma lem1263533 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1263534 (m : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term124 x m n) = (term125 x).
Proof. exact (MK_COMB (@lem1263533) (@lem1263532 m x n h1)). Qed.
Lemma lem1263539 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1263540 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1263541 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (dest_nadd x n) = (term123 x).
Proof. exact (MK_COMB (@lem1263540 x) (@lem1263539 n h1)). Qed.
Lemma lem1263542 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1263543 (m : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term117 m x n) = (term126 m x).
Proof. exact (MK_COMB (@lem1263542 m) (@lem1263541 x n h1)). Qed.
Lemma lem1263547 (m : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term127 m x n) = (term128 m x).
Proof. exact (MK_COMB (@lem1263534 m x n h1) (@lem1263543 m x n h1)). Qed.
Lemma lem1263548 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1263549 (m : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term129 m x n) = (term130 m x).
Proof. exact (MK_COMB (@lem1263548) (@lem1263547 m x n h1)). Qed.
Lemma lem1263551 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term23 m n p).
Proof. exact (EQ_MP (@lem1263478 m n p) (@lem1263477 m n p)). Qed.
Lemma lem1263552 (B : nat) (x : nadd) (m : nat) : (term131 B x m) = (term132 B x m).
Proof. exact (@lem1263551 B (term123 x) m). Qed.
Lemma lem1263557 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1263558 (m : nat) (x : nadd) : (term133 x m) = (term126 m x).
Proof. exact (@lem1263557 m (term123 x)). Qed.
Lemma lem1263562 (B : nat) (m : nat) : (term134 B m) = (term134 B m).
Proof. exact (eq_refl (term134 B m)). Qed.
Lemma lem1263563 (B : nat) (m : nat) (x : nadd) : (term132 B x m) = (term135 B m x).
Proof. exact (MK_COMB (@lem1263562 B m) (@lem1263558 m x)). Qed.
Lemma lem1263564 (B : nat) (m : nat) (x : nadd) : (term131 B x m) = (term135 B m x).
Proof. exact (TRANS (@lem1263552 B x m) (@lem1263563 B m x)). Qed.
Lemma lem1263565 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1263566 (B : nat) (m : nat) (x : nadd) : (term136 B x m) = (term137 B m x).
Proof. exact (MK_COMB (@lem1263565) (@lem1263564 B m x)). Qed.
Lemma lem1263567 (B : nat) (x : nadd) : (term138 B x) = (term138 B x).
Proof. exact (eq_refl (term138 B x)). Qed.
Lemma lem1263568 (m : nat) (B : nat) (x : nadd) : (term118 m B x) = (term139 m B x).
Proof. exact (MK_COMB (@lem1263566 B m x) (@lem1263567 B x)). Qed.
Lemma lem1263569 (m : nat) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term140 n m B x) = (term141 m B x).
Proof. exact (MK_COMB (@lem1263549 m x n h1) (@lem1263568 m B x)). Qed.
Lemma lem1263570 (m : nat) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term141 m B x) = (term140 n m B x).
Proof. exact (SYM (@lem1263569 m B x n h1)). Qed.
Lemma lem1263572 (n : nat) (m : nat) : (Peano.le m n) = (term27 n m).
Proof. exact (EQ_MP (@lem1263387 n m) (@lem1263386 m n)). Qed.
Lemma lem1263573 (B : nat) (m : nat) (x : nadd) : (term141 m B x) = (term142 B m x).
Proof. exact (@lem1263572 (term139 m B x) (term128 m x)). Qed.
Lemma lem1263580 (m : nat) (B : nat) (x : nadd) : (term142 B m x) = (term141 m B x).
Proof. exact (SYM (@lem1263573 B m x)). Qed.
Lemma lem1263584 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (term144 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1263585 (m : nat) (B : nat) (x : nadd) : (term139 m B x) = (term145 m B x).
Proof. exact (@lem1263584 (Nat.mul B m) (term126 m x) (term138 B x)). Qed.
Lemma lem1263593 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263594 (B : nat) (m : nat) (x : nadd) : (term146 m B x) = (term147 B m x).
Proof. exact (@lem1263593 B (term126 m x) (term123 x)). Qed.
Lemma lem1263604 (B : nat) (m : nat) : (term134 B m) = (term134 B m).
Proof. exact (eq_refl (term134 B m)). Qed.
Lemma lem1263605 (B : nat) (m : nat) (x : nadd) : (term145 m B x) = (term148 B m x).
Proof. exact (MK_COMB (@lem1263604 B m) (@lem1263594 B m x)). Qed.
Lemma lem1263607 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263608 (B : nat) (m : nat) (x : nadd) : (term148 B m x) = (term149 B m x).
Proof. exact (@lem1263607 B (Nat.mul B m) (term150 m x)). Qed.
Lemma lem1263624 (B : nat) (m : nat) (x : nadd) : (term145 m B x) = (term149 B m x).
Proof. exact (TRANS (@lem1263605 B m x) (@lem1263608 B m x)). Qed.
Lemma lem1263625 (B : nat) (m : nat) (x : nadd) : (term139 m B x) = (term149 B m x).
Proof. exact (TRANS (@lem1263585 m B x) (@lem1263624 B m x)). Qed.
Lemma lem1263626 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1263627 (B : nat) (m : nat) (x : nadd) : (term151 m B x) = (term152 B m x).
Proof. exact (MK_COMB (@lem1263626) (@lem1263625 B m x)). Qed.
Lemma lem1263629 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263630 (x : nadd) (m : nat) (B : nat) : (term153 x m B) = (term154 x m B).
Proof. exact (@lem1263629 (term126 m x) (term123 x) (term155 m B)). Qed.
Lemma lem1263638 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263639 (m : nat) (x : nadd) (B : nat) : (term156 x m B) = (term157 m x B).
Proof. exact (@lem1263638 (Nat.mul B m) (term123 x) B). Qed.
Lemma lem1263647 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1263648 (B : nat) (x : nadd) : (term158 x B) = (term138 B x).
Proof. exact (@lem1263647 B (term123 x)). Qed.
Lemma lem1263652 (B : nat) (m : nat) : (term134 B m) = (term134 B m).
Proof. exact (eq_refl (term134 B m)). Qed.
Lemma lem1263653 (m : nat) (B : nat) (x : nadd) : (term157 m x B) = (term159 m B x).
Proof. exact (MK_COMB (@lem1263652 B m) (@lem1263648 B x)). Qed.
Lemma lem1263655 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263656 (B : nat) (m : nat) (x : nadd) : (term159 m B x) = (term160 B m x).
Proof. exact (@lem1263655 B (Nat.mul B m) (term123 x)). Qed.
Lemma lem1263666 (B : nat) (m : nat) (x : nadd) : (term157 m x B) = (term160 B m x).
Proof. exact (TRANS (@lem1263653 m B x) (@lem1263656 B m x)). Qed.
Lemma lem1263667 (B : nat) (m : nat) (x : nadd) : (term156 x m B) = (term160 B m x).
Proof. exact (TRANS (@lem1263639 m x B) (@lem1263666 B m x)). Qed.
Lemma lem1263668 (m : nat) (x : nadd) : (term161 m x) = (term161 m x).
Proof. exact (eq_refl (term161 m x)). Qed.
Lemma lem1263669 (B : nat) (m : nat) (x : nadd) : (term154 x m B) = (term162 B m x).
Proof. exact (MK_COMB (@lem1263668 m x) (@lem1263667 B m x)). Qed.
Lemma lem1263671 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263672 (B : nat) (m : nat) (x : nadd) : (term162 B m x) = (term163 B m x).
Proof. exact (@lem1263671 B (term126 m x) (term164 B m x)). Qed.
Lemma lem1263680 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263681 (B : nat) (m : nat) (x : nadd) : (term165 B m x) = (term166 B m x).
Proof. exact (@lem1263680 (Nat.mul B m) (term126 m x) (term123 x)). Qed.
Lemma lem1263691 (B : nat) : (Nat.add B) = (Nat.add B).
Proof. exact (eq_refl (Nat.add B)). Qed.
Lemma lem1263692 (B : nat) (m : nat) (x : nadd) : (term163 B m x) = (term149 B m x).
Proof. exact (MK_COMB (@lem1263691 B) (@lem1263681 B m x)). Qed.
Lemma lem1263699 (B : nat) (m : nat) (x : nadd) : (term162 B m x) = (term149 B m x).
Proof. exact (TRANS (@lem1263672 B m x) (@lem1263692 B m x)). Qed.
Lemma lem1263700 (B : nat) (m : nat) (x : nadd) : (term154 x m B) = (term149 B m x).
Proof. exact (TRANS (@lem1263669 B m x) (@lem1263699 B m x)). Qed.
Lemma lem1263701 (B : nat) (m : nat) (x : nadd) : (term153 x m B) = (term149 B m x).
Proof. exact (TRANS (@lem1263630 x m B) (@lem1263700 B m x)). Qed.
Lemma lem1263702 (B : nat) (m : nat) (x : nadd) : ((term139 m B x) = (term153 x m B)) = ((term149 B m x) = (term149 B m x)).
Proof. exact (MK_COMB (@lem1263627 B m x) (@lem1263701 B m x)). Qed.
Lemma lem1263704 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1263705 (x : nat) : (x = x) = True.
Proof. exact (@lem1263704 nat x). Qed.
Lemma lem1263706 (B : nat) (m : nat) (x : nadd) : ((term149 B m x) = (term149 B m x)) = True.
Proof. exact (@lem1263705 (term149 B m x)). Qed.
Lemma lem1263707 (x : nadd) (m : nat) (B : nat) : ((term139 m B x) = (term153 x m B)) = True.
Proof. exact (TRANS (@lem1263702 B m x) (@lem1263706 B m x)). Qed.
Lemma lem1263708 (x : nadd) (m : nat) (B : nat) : True = ((term139 m B x) = (term153 x m B)).
Proof. exact (SYM (@lem1263707 x m B)). Qed.
Lemma lem1263709 (x : nadd) (m : nat) (B : nat) : (term139 m B x) = (term153 x m B).
Proof. exact (EQ_MP (@lem1263708 x m B) (@lem0)). Qed.
Lemma lem1263713 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (term144 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1263714 (m : nat) (x : nadd) (d : nat) : (term167 m x d) = (term168 m x d).
Proof. exact (@lem1263713 (term123 x) (term126 m x) d). Qed.
Lemma lem1263716 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263717 (m : nat) (x : nadd) (d : nat) : (term168 m x d) = (term169 m x d).
Proof. exact (@lem1263716 (term126 m x) (term123 x) d). Qed.
Lemma lem1263724 (m : nat) (x : nadd) (d : nat) : (term167 m x d) = (term169 m x d).
Proof. exact (TRANS (@lem1263714 m x d) (@lem1263717 m x d)). Qed.
Lemma lem1263726 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1263727 (d : nat) (x : nadd) : (term158 x d) = (term138 d x).
Proof. exact (@lem1263726 d (term123 x)). Qed.
Lemma lem1263731 (m : nat) (x : nadd) : (term161 m x) = (term161 m x).
Proof. exact (eq_refl (term161 m x)). Qed.
Lemma lem1263732 (m : nat) (d : nat) (x : nadd) : (term169 m x d) = (term146 m d x).
Proof. exact (MK_COMB (@lem1263731 m x) (@lem1263727 d x)). Qed.
Lemma lem1263734 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263735 (d : nat) (m : nat) (x : nadd) : (term146 m d x) = (term147 d m x).
Proof. exact (@lem1263734 d (term126 m x) (term123 x)). Qed.
Lemma lem1263745 (d : nat) (m : nat) (x : nadd) : (term169 m x d) = (term147 d m x).
Proof. exact (TRANS (@lem1263732 m d x) (@lem1263735 d m x)). Qed.
Lemma lem1263746 (d : nat) (m : nat) (x : nadd) : (term167 m x d) = (term147 d m x).
Proof. exact (TRANS (@lem1263724 m x d) (@lem1263745 d m x)). Qed.
Lemma lem1263747 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1263748 (d : nat) (m : nat) (x : nadd) : (term170 m x d) = (term171 d m x).
Proof. exact (MK_COMB (@lem1263747) (@lem1263746 d m x)). Qed.
Lemma lem1263750 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263751 (m : nat) (x : nadd) (d : nat) : (term168 m x d) = (term169 m x d).
Proof. exact (@lem1263750 (term126 m x) (term123 x) d). Qed.
Lemma lem1263759 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1263760 (d : nat) (x : nadd) : (term158 x d) = (term138 d x).
Proof. exact (@lem1263759 d (term123 x)). Qed.
Lemma lem1263764 (m : nat) (x : nadd) : (term161 m x) = (term161 m x).
Proof. exact (eq_refl (term161 m x)). Qed.
Lemma lem1263765 (m : nat) (d : nat) (x : nadd) : (term169 m x d) = (term146 m d x).
Proof. exact (MK_COMB (@lem1263764 m x) (@lem1263760 d x)). Qed.
Lemma lem1263767 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1263768 (d : nat) (m : nat) (x : nadd) : (term146 m d x) = (term147 d m x).
Proof. exact (@lem1263767 d (term126 m x) (term123 x)). Qed.
Lemma lem1263778 (d : nat) (m : nat) (x : nadd) : (term169 m x d) = (term147 d m x).
Proof. exact (TRANS (@lem1263765 m d x) (@lem1263768 d m x)). Qed.
Lemma lem1263779 (d : nat) (m : nat) (x : nadd) : (term168 m x d) = (term147 d m x).
Proof. exact (TRANS (@lem1263751 m x d) (@lem1263778 d m x)). Qed.
Lemma lem1263780 (d : nat) (m : nat) (x : nadd) : ((term167 m x d) = (term168 m x d)) = ((term147 d m x) = (term147 d m x)).
Proof. exact (MK_COMB (@lem1263748 d m x) (@lem1263779 d m x)). Qed.
Lemma lem1263782 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1263783 (x : nat) : (x = x) = True.
Proof. exact (@lem1263782 nat x). Qed.
Lemma lem1263784 (d : nat) (m : nat) (x : nadd) : ((term147 d m x) = (term147 d m x)) = True.
Proof. exact (@lem1263783 (term147 d m x)). Qed.
Lemma lem1263785 (m : nat) (x : nadd) (d : nat) : ((term167 m x d) = (term168 m x d)) = True.
Proof. exact (TRANS (@lem1263780 d m x) (@lem1263784 d m x)). Qed.
Lemma lem1263786 (m : nat) (x : nadd) (d : nat) : True = ((term167 m x d) = (term168 m x d)).
Proof. exact (SYM (@lem1263785 m x d)). Qed.
Lemma lem1263787 (m : nat) (x : nadd) (d : nat) : (term167 m x d) = (term168 m x d).
Proof. exact (EQ_MP (@lem1263786 m x d) (@lem0)). Qed.
Lemma lem1263788 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1263789 (x : nadd) (m : nat) (B : nat) : (term151 m B x) = (term172 x m B).
Proof. exact (MK_COMB (@lem1263788) (@lem1263709 x m B)). Qed.
Lemma lem1263790 (B : nat) (m : nat) (x : nadd) (d : nat) : ((term139 m B x) = (term167 m x d)) = ((term153 x m B) = (term168 m x d)).
Proof. exact (MK_COMB (@lem1263789 x m B) (@lem1263787 m x d)). Qed.
Lemma lem1263803 (m : nat) : term173 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1263804 (m : nat) : (term173 m) = (term174 m).
Proof. exact (eq_refl (term173 m)). Qed.
Lemma lem1263805 (m : nat) : term174 m.
Proof. exact (EQ_MP (@lem1263804 m) (@lem1263803 m)). Qed.
Lemma lem1263806 (m : nat) (n : nat) : term175 m n.
Proof. exact (@lem1263805 m n). Qed.
Lemma lem1263807 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (eq_refl (term175 m n)). Qed.
Lemma lem1263808 (m : nat) (n : nat) : term176 m n.
Proof. exact (EQ_MP (@lem1263807 m n) (@lem1263806 m n)). Qed.
Lemma lem1263809 (m : nat) (n : nat) (p : nat) : term177 m n p.
Proof. exact (@lem1263808 m n p). Qed.
Lemma lem1263810 (m : nat) (n : nat) (p : nat) : (term177 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term177 m n p)). Qed.
Lemma lem1263813 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1263810 m n p) (@lem1263809 m n p)). Qed.
Lemma lem1263814 (B : nat) (m : nat) (x : nadd) (d : nat) : ((term153 x m B) = (term168 m x d)) = ((term178 x m B) = (term179 m x d)).
Proof. exact (@lem1263813 (term123 x) (term178 x m B) (term179 m x d)). Qed.
Lemma lem1263816 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1263810 m n p) (@lem1263809 m n p)). Qed.
Lemma lem1263821 (x : nadd) (m : nat) (B : nat) (d : nat) : ((term178 x m B) = (term179 m x d)) = ((term155 m B) = d).
Proof. exact (@lem1263816 (term126 m x) (term155 m B) d). Qed.
Lemma lem1263822 (x : nadd) (m : nat) (B : nat) (d : nat) : ((term153 x m B) = (term168 m x d)) = ((term155 m B) = d).
Proof. exact (TRANS (@lem1263814 B m x d) (@lem1263821 x m B d)). Qed.
Lemma lem1263823 (B : nat) (m : nat) (x : nadd) (d : nat) : (term180 B m x d) = (term180 B m x d).
Proof. exact (eq_refl (term180 B m x d)). Qed.
Lemma lem1263824 (x : nadd) (m : nat) (B : nat) (d : nat) : (((term139 m B x) = (term167 m x d)) = ((term153 x m B) = (term168 m x d))) = (((term139 m B x) = (term167 m x d)) = ((term155 m B) = d)).
Proof. exact (MK_COMB (@lem1263823 B m x d) (@lem1263822 x m B d)). Qed.
Lemma lem1263825 (x : nadd) (m : nat) (B : nat) (d : nat) : ((term139 m B x) = (term167 m x d)) = ((term155 m B) = d).
Proof. exact (EQ_MP (@lem1263824 x m B d) (@lem1263790 B m x d)). Qed.
Lemma lem1263826 (x : nadd) (m : nat) (B : nat) : (term181 B m x) = (term182 m B).
Proof. exact (fun_ext (fun d : nat => @lem1263825 x m B d)). Qed.
Lemma lem1263827 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1263828 (x : nadd) (m : nat) (B : nat) : (term142 B m x) = (term183 m B).
Proof. exact (MK_COMB (@lem1263827) (@lem1263826 x m B)). Qed.
Lemma lem1263829 (B : nat) (m : nat) (x : nadd) : (term183 m B) = (term142 B m x).
Proof. exact (SYM (@lem1263828 x m B)). Qed.
Lemma lem1263831 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem1263381 A a) (@lem1263380 A a)). Qed.
Lemma lem1263832 (a : nat) : (term184 a) = True.
Proof. exact (@lem1263831 nat a). Qed.
Lemma lem1263833 (m : nat) (B : nat) : (term183 m B) = True.
Proof. exact (@lem1263832 (term155 m B)). Qed.
Lemma lem1263834 (m : nat) (B : nat) : True = (term183 m B).
Proof. exact (SYM (@lem1263833 m B)). Qed.
Lemma lem1263835 (m : nat) (B : nat) : term183 m B.
Proof. exact (EQ_MP (@lem1263834 m B) (@lem0)). Qed.
Lemma lem1263836 (B : nat) (m : nat) (x : nadd) : term142 B m x.
Proof. exact (EQ_MP (@lem1263829 B m x) (@lem1263835 m B)). Qed.
Lemma lem1263837 (m : nat) (B : nat) (x : nadd) : term141 m B x.
Proof. exact (EQ_MP (@lem1263580 m B x) (@lem1263836 B m x)). Qed.
Lemma lem1263838 (m : nat) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : term140 n m B x.
Proof. exact (EQ_MP (@lem1263570 m B x n h1) (@lem1263837 m B x)). Qed.
Lemma lem1263839 (m : nat) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : term185 n m B x.
Proof. exact (@lem1263466 n m B x (@lem1263838 m B x n h1)). Qed.
Lemma lem1263841 (a : Prop) (b : Prop) : (term59 a b) = (a \/ b).
Proof. exact (or_elim (@lem1263251 a) (fun h0 : a = True => @lem1263342 b a h0) (fun h0 : a = False => @lem1263341 b a h0)). Qed.
Lemma lem1263842 (n : nat) (m : nat) (B : nat) (x : nadd) : (term186 n m B x) = (term187 n m B x).
Proof. exact (@lem1263841 (n = (NUMERAL 0)) (term185 n m B x)). Qed.
Lemma lem1263844 (n : nat) (m : nat) (p : nat) : (term39 m n p) = (term38 n m p).
Proof. exact (EQ_MP (@lem1263362 n m p) (@lem1263361 n m p)). Qed.
Lemma lem1263845 (n : nat) (m : nat) (B : nat) (x : nadd) : (term187 n m B x) = (term188 n m B x).
Proof. exact (@lem1263844 (term189 m x n) n (term118 m B x)). Qed.
Lemma lem1263846 (n : nat) (m : nat) (B : nat) (x : nadd) : (term186 n m B x) = (term188 n m B x).
Proof. exact (TRANS (@lem1263842 n m B x) (@lem1263845 n m B x)). Qed.
Lemma lem1263848 (n : nat) (m : nat) (p : nat) : (term72 m n p) = (term73 n m p).
Proof. exact (EQ_MP (@lem1263353 n m p) (@lem1263352 n m p)). Qed.
Lemma lem1263849 (m : nat) (x : nadd) (n : nat) : (term190 m x n) = (term191 m x n).
Proof. exact (@lem1263848 (term116 x m n) n (term117 m x n)). Qed.
Lemma lem1263850 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1263851 (m : nat) (x : nadd) (n : nat) : (term192 m x n) = (term193 m x n).
Proof. exact (MK_COMB (@lem1263850) (@lem1263849 m x n)). Qed.
Lemma lem1263852 (n : nat) (m : nat) (B : nat) (x : nadd) : (term194 n m B x) = (term194 n m B x).
Proof. exact (eq_refl (term194 n m B x)). Qed.
Lemma lem1263853 (n : nat) (m : nat) (B : nat) (x : nadd) : (term188 n m B x) = (term195 n m B x).
Proof. exact (MK_COMB (@lem1263851 m x n) (@lem1263852 n m B x)). Qed.
Lemma lem1263854 (n : nat) (m : nat) (B : nat) (x : nadd) : (term186 n m B x) = (term195 n m B x).
Proof. exact (TRANS (@lem1263846 n m B x) (@lem1263853 n m B x)). Qed.
Lemma lem1263855 (n : nat) (m : nat) (B : nat) (x : nadd) : (term195 n m B x) = (term186 n m B x).
Proof. exact (SYM (@lem1263854 n m B x)). Qed.
Lemma lem1263857 (m : nat) (n : nat) (p : nat) : (term36 m n p) = (term37 m n p).
Proof. exact (EQ_MP (@lem1263221 m n p) (@lem1263220 m n p)). Qed.
Lemma lem1263858 (m : nat) (x : nadd) (n : nat) : (term196 m x n) = (term197 m x n).
Proof. exact (@lem1263857 n m (dest_nadd x n)). Qed.
Lemma lem1263859 (x : nadd) (m : nat) (n : nat) : (term198 x m n) = (term198 x m n).
Proof. exact (eq_refl (term198 x m n)). Qed.
Lemma lem1263860 (m : nat) (x : nadd) (n : nat) : (term199 m x n) = (term200 m x n).
Proof. exact (MK_COMB (@lem1263859 x m n) (@lem1263858 m x n)). Qed.
Lemma lem1263861 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1263862 (m : nat) (x : nadd) (n : nat) : (term191 m x n) = (term201 m x n).
Proof. exact (MK_COMB (@lem1263861) (@lem1263860 m x n)). Qed.
Lemma lem1263863 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1263864 (m : nat) (x : nadd) (n : nat) : (term193 m x n) = (term202 m x n).
Proof. exact (MK_COMB (@lem1263863) (@lem1263862 m x n)). Qed.
Lemma lem1263865 (n : nat) (m : nat) (B : nat) (x : nadd) : (term194 n m B x) = (term194 n m B x).
Proof. exact (eq_refl (term194 n m B x)). Qed.
Lemma lem1263866 (n : nat) (m : nat) (B : nat) (x : nadd) : (term195 n m B x) = (term203 n m B x).
Proof. exact (MK_COMB (@lem1263864 m x n) (@lem1263865 n m B x)). Qed.
Lemma lem1263867 (n : nat) (m : nat) (B : nat) (x : nadd) : (term203 n m B x) = (term195 n m B x).
Proof. exact (SYM (@lem1263866 n m B x)). Qed.
Lemma lem1263869 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1263212 n m) (@lem1263211 m n)). Qed.
Lemma lem1263870 (m : nat) (n : nat) : (Nat.mul n m) = (Nat.mul m n).
Proof. exact (@lem1263869 m n). Qed.
Lemma lem1263871 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1263872 (m : nat) (n : nat) : (term204 n m) = (term204 m n).
Proof. exact (MK_COMB (@lem1263871) (@lem1263870 m n)). Qed.
Lemma lem1263873 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1263874 (m : nat) (x : nadd) (n : nat) : (term197 m x n) = (term205 m x n).
Proof. exact (MK_COMB (@lem1263872 m n) (@lem1263873 x n)). Qed.
Lemma lem1263875 (x : nadd) (m : nat) (n : nat) : (term198 x m n) = (term198 x m n).
Proof. exact (eq_refl (term198 x m n)). Qed.
Lemma lem1263876 (m : nat) (x : nadd) (n : nat) : (term200 m x n) = (term206 m x n).
Proof. exact (MK_COMB (@lem1263875 x m n) (@lem1263874 m x n)). Qed.
Lemma lem1263877 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1263878 (m : nat) (x : nadd) (n : nat) : (term201 m x n) = (term207 m x n).
Proof. exact (MK_COMB (@lem1263877) (@lem1263876 m x n)). Qed.
Lemma lem1263879 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1263880 (m : nat) (x : nadd) (n : nat) : (term202 m x n) = (term208 m x n).
Proof. exact (MK_COMB (@lem1263879) (@lem1263878 m x n)). Qed.
Lemma lem1263881 (n : nat) (m : nat) (B : nat) (x : nadd) : (term194 n m B x) = (term194 n m B x).
Proof. exact (eq_refl (term194 n m B x)). Qed.
Lemma lem1263882 (n : nat) (m : nat) (B : nat) (x : nadd) : (term203 n m B x) = (term209 n m B x).
Proof. exact (MK_COMB (@lem1263880 m x n) (@lem1263881 n m B x)). Qed.
Lemma lem1263883 (n : nat) (m : nat) (B : nat) (x : nadd) : (term209 n m B x) = (term203 n m B x).
Proof. exact (SYM (@lem1263882 n m B x)). Qed.
Lemma lem1263884 (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term210 x B m.
Proof. exact (@lem1263463 x B h1 m). Qed.
Lemma lem1263885 (x : nadd) (B : nat) (m : nat) : (term210 x B m) = (term211 x B m).
Proof. exact (eq_refl (term210 x B m)). Qed.
Lemma lem1263886 (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term211 x B m.
Proof. exact (EQ_MP (@lem1263885 x B m) (@lem1263884 m x B h1)). Qed.
Lemma lem1263887 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term212 x B m n.
Proof. exact (@lem1263886 m x B h1 n). Qed.
Lemma lem1263888 (x : nadd) (B : nat) (m : nat) (n : nat) : (term212 x B m n) = (term213 x B m n).
Proof. exact (eq_refl (term212 x B m n)). Qed.
Lemma lem1263889 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term213 x B m n.
Proof. exact (EQ_MP (@lem1263888 x B m n) (@lem1263887 m n x B h1)). Qed.
Lemma lem1263890 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem1263891 (m : nat) (h1 : term81) : term82 m.
Proof. exact (@lem1263890 h1 m). Qed.
Lemma lem1263892 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1263893 (m : nat) (h1 : term81) : term83 m.
Proof. exact (EQ_MP (@lem1263892 m) (@lem1263891 m h1)). Qed.
Lemma lem1263894 (m : nat) (n : nat) (h1 : term81) : term84 m n.
Proof. exact (@lem1263893 m h1 n). Qed.
Lemma lem1263895 (n : nat) (m : nat) : (term84 m n) = (term85 n m).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1263896 (n : nat) (m : nat) (h1 : term81) : term85 n m.
Proof. exact (EQ_MP (@lem1263895 n m) (@lem1263894 m n h1)). Qed.
Lemma lem1263897 (n : nat) (m : nat) (p : nat) (h1 : term81) : term86 n m p.
Proof. exact (@lem1263896 n m h1 p). Qed.
Lemma lem1263898 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term87 n m p).
Proof. exact (eq_refl (term86 n m p)). Qed.
Lemma lem1263899 (n : nat) (m : nat) (p : nat) (h1 : term81) : term87 n m p.
Proof. exact (EQ_MP (@lem1263898 n m p) (@lem1263897 n m p h1)). Qed.
Lemma lem1263900 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1263901 (p : nat) (m : nat) (n : nat) (h1 : term81) (h2 : Peano.le m n) : term88 n m p.
Proof. exact (@lem1263899 n m p h1 (@lem1263900 m n h2)). Qed.
Lemma lem1263902 (m : nat) (n : nat) (h1 : term81) (h2 : Peano.le m n) : term89 n m.
Proof. exact (fun p : nat => @lem1263901 p m n h1 h2). Qed.
Lemma lem1263903 (n : nat) (m : nat) (h1 : term81) : term90 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1263902 m n h1 h0). Qed.
Lemma lem1263904 (m : nat) (h1 : term81) : term91 m.
Proof. exact (fun n : nat => @lem1263903 n m h1). Qed.
Lemma lem1263905 (h1 : term81) : term92.
Proof. exact (fun m : nat => @lem1263904 m h1). Qed.
Lemma lem1263906 : term93.
Proof. exact (fun h0 : term81 => @lem1263905 h0). Qed.
Lemma lem1263907 : term92.
Proof. exact (@lem1263906 (@lem272809)). Qed.
Lemma lem1263908 (m : nat) : term94 m.
Proof. exact (@lem1263907 m). Qed.
Lemma lem1263909 (m : nat) : (term94 m) = (term91 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem1263910 (m : nat) : term91 m.
Proof. exact (EQ_MP (@lem1263909 m) (@lem1263908 m)). Qed.
Lemma lem1263911 (m : nat) (n : nat) : term95 m n.
Proof. exact (@lem1263910 m n). Qed.
Lemma lem1263912 (n : nat) (m : nat) : (term95 m n) = (term90 n m).
Proof. exact (eq_refl (term95 m n)). Qed.
Lemma lem1263915 (n : nat) (m : nat) : term90 n m.
Proof. exact (EQ_MP (@lem1263912 n m) (@lem1263911 m n)). Qed.
Lemma lem1263916 (B : nat) (n : nat) (x : nadd) (m : nat) : term214 B n x m.
Proof. exact (@lem1263915 (term15 B m n) (term215 n x m)). Qed.
Lemma lem1263917 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term216 B n x m.
Proof. exact (@lem1263916 B n x m (@lem1263889 m n x B h1)). Qed.
Lemma lem1263918 (n : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term217 B n x.
Proof. exact (fun m : nat => @lem1263917 n m x B h1). Qed.
Lemma lem1263919 (x : nadd) (B : nat) (h1 : term114 x B) : term218 B x.
Proof. exact (fun n : nat => @lem1263918 n x B h1). Qed.
Lemma lem1263920 (B : nat) (x : nadd) (h1 : term218 B x) : term218 B x.
Proof. exact (h1). Qed.
Lemma lem1263921 (n : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term219 B x n.
Proof. exact (@lem1263920 B x h1 n). Qed.
Lemma lem1263922 (B : nat) (n : nat) (x : nadd) : (term219 B x n) = (term217 B n x).
Proof. exact (eq_refl (term219 B x n)). Qed.
Lemma lem1263923 (n : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term217 B n x.
Proof. exact (EQ_MP (@lem1263922 B n x) (@lem1263921 n B x h1)). Qed.
Lemma lem1263924 (n : nat) (m : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term220 B n x m.
Proof. exact (@lem1263923 n B x h1 m). Qed.
Lemma lem1263925 (B : nat) (n : nat) (x : nadd) (m : nat) : (term220 B n x m) = (term216 B n x m).
Proof. exact (eq_refl (term220 B n x m)). Qed.
Lemma lem1263926 (n : nat) (m : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term216 B n x m.
Proof. exact (EQ_MP (@lem1263925 B n x m) (@lem1263924 n m B x h1)). Qed.
Lemma lem1263927 (n : nat) (m : nat) (p : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term221 B n x m p.
Proof. exact (@lem1263926 n m B x h1 p). Qed.
Lemma lem1263928 (B : nat) (n : nat) (x : nadd) (m : nat) (p : nat) : (term221 B n x m p) = (term222 B n x m p).
Proof. exact (eq_refl (term221 B n x m p)). Qed.
Lemma lem1263929 (n : nat) (m : nat) (p : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term222 B n x m p.
Proof. exact (EQ_MP (@lem1263928 B n x m p) (@lem1263927 n m p B x h1)). Qed.
Lemma lem1263930 (B : nat) (m : nat) (n : nat) (p : nat) (h1 : term223 B m n p) : term223 B m n p.
Proof. exact (h1). Qed.
Lemma lem1263931 (x : nadd) (B : nat) (m : nat) (n : nat) (p : nat) (h1 : term218 B x) (h2 : term223 B m n p) : term224 n x m p.
Proof. exact (@lem1263929 n m p B x h1 (@lem1263930 B m n p h2)). Qed.
Lemma lem1263932 (x : nadd) (B : nat) (m : nat) (n : nat) (p : nat) (h1 : term223 B m n p) : term225 B n x m p.
Proof. exact (fun h0 : term218 B x => @lem1263931 x B m n p h0 h1). Qed.
Lemma lem1263933 (B : nat) (x : nadd) (h1 : term218 B x) : term218 B x.
Proof. exact (h1). Qed.
Lemma lem1263934 (x : nadd) (B : nat) (m : nat) (n : nat) (p : nat) (h1 : term218 B x) (h2 : term223 B m n p) : term224 n x m p.
Proof. exact (@lem1263932 x B m n p h2 (@lem1263933 B x h1)). Qed.
Lemma lem1263935 (n : nat) (m : nat) (p : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term222 B n x m p.
Proof. exact (fun h0 : term223 B m n p => @lem1263934 x B m n p h1 h0). Qed.
Lemma lem1263936 (n : nat) (m : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term216 B n x m.
Proof. exact (fun p : nat => @lem1263935 n m p B x h1). Qed.
Lemma lem1263937 (n : nat) (B : nat) (x : nadd) (h1 : term218 B x) : term217 B n x.
Proof. exact (fun m : nat => @lem1263936 n m B x h1). Qed.
Lemma lem1263938 (B : nat) (x : nadd) (h1 : term218 B x) : term218 B x.
Proof. exact (fun n : nat => @lem1263937 n B x h1). Qed.
Lemma lem1263939 (B : nat) (x : nadd) : term226 B x.
Proof. exact (fun h0 : term218 B x => @lem1263938 B x h0). Qed.
Lemma lem1263940 (x : nadd) (B : nat) (h1 : term114 x B) : term218 B x.
Proof. exact (@lem1263939 B x (@lem1263919 x B h1)). Qed.
Lemma lem1263941 (n : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term219 B x n.
Proof. exact (@lem1263940 x B h1 n). Qed.
Lemma lem1263942 (B : nat) (n : nat) (x : nadd) : (term219 B x n) = (term217 B n x).
Proof. exact (eq_refl (term219 B x n)). Qed.
Lemma lem1263943 (n : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term217 B n x.
Proof. exact (EQ_MP (@lem1263942 B n x) (@lem1263941 n x B h1)). Qed.
Lemma lem1263944 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term220 B n x m.
Proof. exact (@lem1263943 n x B h1 m). Qed.
Lemma lem1263945 (B : nat) (n : nat) (x : nadd) (m : nat) : (term220 B n x m) = (term216 B n x m).
Proof. exact (eq_refl (term220 B n x m)). Qed.
Lemma lem1263946 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term216 B n x m.
Proof. exact (EQ_MP (@lem1263945 B n x m) (@lem1263944 n m x B h1)). Qed.
Lemma lem1263947 (n : nat) (m : nat) (p : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term221 B n x m p.
Proof. exact (@lem1263946 n m x B h1 p). Qed.
Lemma lem1263948 (B : nat) (n : nat) (x : nadd) (m : nat) (p : nat) : (term221 B n x m p) = (term222 B n x m p).
Proof. exact (eq_refl (term221 B n x m p)). Qed.
Lemma lem1263951 (n : nat) (m : nat) (p : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term222 B n x m p.
Proof. exact (EQ_MP (@lem1263948 B n x m p) (@lem1263947 n m p x B h1)). Qed.
Lemma lem1263952 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term227 n m B x.
Proof. exact (@lem1263951 (Nat.mul m n) n (term194 n m B x) x B h1). Qed.
Lemma lem1263954 (n : nat) (m : nat) : (Peano.le m n) = (term27 n m).
Proof. exact (EQ_MP (@lem1263206 n m) (@lem1263205 m n)). Qed.
Lemma lem1263955 (x : nadd) (B : nat) (m : nat) (n : nat) : (term228 n m B x) = (term229 x B m n).
Proof. exact (@lem1263954 (term194 n m B x) (term230 B m n)). Qed.
Lemma lem1263963 (n : nat) (m : nat) (p : nat) : (term15 m n p) = (term16 n m p).
Proof. exact (EQ_MP (@lem1263191 n m p) (@lem1263190 n m p)). Qed.
Lemma lem1263964 (m : nat) (n : nat) (B : nat) (x : nadd) : (term194 n m B x) = (term231 m n B x).
Proof. exact (@lem1263963 (term131 B x m) n (term138 B x)). Qed.
Lemma lem1263972 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term23 m n p).
Proof. exact (EQ_MP (@lem1263200 m n p) (@lem1263199 m n p)). Qed.
Lemma lem1263973 (B : nat) (x : nadd) (m : nat) : (term131 B x m) = (term132 B x m).
Proof. exact (@lem1263972 B (term123 x) m). Qed.
Lemma lem1263978 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1263979 (m : nat) (x : nadd) : (term133 x m) = (term126 m x).
Proof. exact (@lem1263978 m (term123 x)). Qed.
Lemma lem1263983 (B : nat) (m : nat) : (term134 B m) = (term134 B m).
Proof. exact (eq_refl (term134 B m)). Qed.
Lemma lem1263984 (B : nat) (m : nat) (x : nadd) : (term132 B x m) = (term135 B m x).
Proof. exact (MK_COMB (@lem1263983 B m) (@lem1263979 m x)). Qed.
Lemma lem1263985 (B : nat) (m : nat) (x : nadd) : (term131 B x m) = (term135 B m x).
Proof. exact (TRANS (@lem1263973 B x m) (@lem1263984 B m x)). Qed.
Lemma lem1263986 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1263987 (n : nat) (B : nat) (m : nat) (x : nadd) : (term232 n B x m) = (term233 n B m x).
Proof. exact (MK_COMB (@lem1263986 n) (@lem1263985 B m x)). Qed.
Lemma lem1263989 (n : nat) (m : nat) (p : nat) : (term15 m n p) = (term16 n m p).
Proof. exact (EQ_MP (@lem1263191 n m p) (@lem1263190 n m p)). Qed.
Lemma lem1263990 (B : nat) (n : nat) (m : nat) (x : nadd) : (term233 n B m x) = (term234 B n m x).
Proof. exact (@lem1263989 (Nat.mul B m) n (term126 m x)). Qed.
Lemma lem1263992 (n : nat) (m : nat) (p : nat) : (term36 m n p) = (term36 n m p).
Proof. exact (proj2 (@lem1263180 n m p)). Qed.
Lemma lem1263993 (B : nat) (n : nat) (m : nat) : (term36 n B m) = (term36 B n m).
Proof. exact (@lem1263992 B n m). Qed.
Lemma lem1264001 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1264002 (m : nat) (n : nat) : (Nat.mul n m) = (Nat.mul m n).
Proof. exact (@lem1264001 m n). Qed.
Lemma lem1264005 (B : nat) : (Nat.mul B) = (Nat.mul B).
Proof. exact (eq_refl (Nat.mul B)). Qed.
Lemma lem1264006 (B : nat) (m : nat) (n : nat) : (term36 B n m) = (term36 B m n).
Proof. exact (MK_COMB (@lem1264005 B) (@lem1264002 m n)). Qed.
Lemma lem1264013 (B : nat) (m : nat) (n : nat) : (term36 n B m) = (term36 B m n).
Proof. exact (TRANS (@lem1263993 B n m) (@lem1264006 B m n)). Qed.
Lemma lem1264014 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1264015 (B : nat) (m : nat) (n : nat) : (term235 n B m) = (term235 B m n).
Proof. exact (MK_COMB (@lem1264014) (@lem1264013 B m n)). Qed.
Lemma lem1264017 (n : nat) (m : nat) (p : nat) : (term36 m n p) = (term36 n m p).
Proof. exact (proj2 (@lem1263180 n m p)). Qed.
Lemma lem1264018 (m : nat) (n : nat) (x : nadd) : (term236 n m x) = (term236 m n x).
Proof. exact (@lem1264017 m n (term123 x)). Qed.
Lemma lem1264028 (B : nat) (m : nat) (n : nat) (x : nadd) : (term234 B n m x) = (term237 B m n x).
Proof. exact (MK_COMB (@lem1264015 B m n) (@lem1264018 m n x)). Qed.
Lemma lem1264029 (B : nat) (m : nat) (n : nat) (x : nadd) : (term233 n B m x) = (term237 B m n x).
Proof. exact (TRANS (@lem1263990 B n m x) (@lem1264028 B m n x)). Qed.
Lemma lem1264030 (B : nat) (m : nat) (n : nat) (x : nadd) : (term232 n B x m) = (term237 B m n x).
Proof. exact (TRANS (@lem1263987 n B m x) (@lem1264029 B m n x)). Qed.
Lemma lem1264031 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1264032 (B : nat) (m : nat) (n : nat) (x : nadd) : (term238 n B x m) = (term239 B m n x).
Proof. exact (MK_COMB (@lem1264031) (@lem1264030 B m n x)). Qed.
Lemma lem1264034 (n : nat) (m : nat) (p : nat) : (term15 m n p) = (term16 n m p).
Proof. exact (EQ_MP (@lem1263191 n m p) (@lem1263190 n m p)). Qed.
Lemma lem1264035 (B : nat) (n : nat) (x : nadd) : (term240 n B x) = (term241 B n x).
Proof. exact (@lem1264034 B n (term123 x)). Qed.
Lemma lem1264037 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1264038 (B : nat) (n : nat) : (Nat.mul n B) = (Nat.mul B n).
Proof. exact (@lem1264037 B n). Qed.
Lemma lem1264042 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1264043 (B : nat) (n : nat) : (term134 n B) = (term134 B n).
Proof. exact (MK_COMB (@lem1264042) (@lem1264038 B n)). Qed.
Lemma lem1264047 (n : nat) (x : nadd) : (term126 n x) = (term126 n x).
Proof. exact (eq_refl (term126 n x)). Qed.
Lemma lem1264048 (B : nat) (n : nat) (x : nadd) : (term241 B n x) = (term135 B n x).
Proof. exact (MK_COMB (@lem1264043 B n) (@lem1264047 n x)). Qed.
Lemma lem1264049 (B : nat) (n : nat) (x : nadd) : (term240 n B x) = (term135 B n x).
Proof. exact (TRANS (@lem1264035 B n x) (@lem1264048 B n x)). Qed.
Lemma lem1264050 (m : nat) (B : nat) (n : nat) (x : nadd) : (term231 m n B x) = (term242 m B n x).
Proof. exact (MK_COMB (@lem1264032 B m n x) (@lem1264049 B n x)). Qed.
Lemma lem1264051 (m : nat) (B : nat) (n : nat) (x : nadd) : (term194 n m B x) = (term242 m B n x).
Proof. exact (TRANS (@lem1263964 m n B x) (@lem1264050 m B n x)). Qed.
Lemma lem1264052 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1264053 (m : nat) (B : nat) (n : nat) (x : nadd) : (term243 n m B x) = (term244 m B n x).
Proof. exact (MK_COMB (@lem1264052) (@lem1264051 m B n x)). Qed.
Lemma lem1264055 (n : nat) (m : nat) (p : nat) : (term15 m n p) = (term16 n m p).
Proof. exact (EQ_MP (@lem1263191 n m p) (@lem1263190 n m p)). Qed.
Lemma lem1264056 (B : nat) (m : nat) (n : nat) : (term230 B m n) = (term245 B m n).
Proof. exact (@lem1264055 n B (Nat.mul m n)). Qed.
Lemma lem1264068 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1264069 (B : nat) (m : nat) (n : nat) : (term246 B m n) = (term247 B m n).
Proof. exact (MK_COMB (@lem1264068) (@lem1264056 B m n)). Qed.
Lemma lem1264070 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1264071 (B : nat) (m : nat) (n : nat) (d : nat) : (term248 B m n d) = (term249 B m n d).
Proof. exact (MK_COMB (@lem1264069 B m n) (@lem1264070 d)). Qed.
Lemma lem1264072 (x : nadd) (B : nat) (m : nat) (n : nat) (d : nat) : ((term194 n m B x) = (term248 B m n d)) = ((term242 m B n x) = (term249 B m n d)).
Proof. exact (MK_COMB (@lem1264053 m B n x) (@lem1264071 B m n d)). Qed.
Lemma lem1264075 (x : nadd) (B : nat) (m : nat) (n : nat) : (term250 x B m n) = (term251 x B m n).
Proof. exact (fun_ext (fun d : nat => @lem1264072 x B m n d)). Qed.
Lemma lem1264076 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1264077 (x : nadd) (B : nat) (m : nat) (n : nat) : (term229 x B m n) = (term252 x B m n).
Proof. exact (MK_COMB (@lem1264076) (@lem1264075 x B m n)). Qed.
Lemma lem1264082 (x : nadd) (B : nat) (m : nat) (n : nat) : (term228 n m B x) = (term252 x B m n).
Proof. exact (TRANS (@lem1263955 x B m n) (@lem1264077 x B m n)). Qed.
Lemma lem1264083 (n : nat) (m : nat) (B : nat) (x : nadd) : (term252 x B m n) = (term228 n m B x).
Proof. exact (SYM (@lem1264082 x B m n)). Qed.
Lemma lem1264087 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (term144 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1264088 (m : nat) (B : nat) (n : nat) (x : nadd) : (term242 m B n x) = (term253 m B n x).
Proof. exact (@lem1264087 (term36 B m n) (term236 m n x) (term135 B n x)). Qed.
Lemma lem1264096 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1264097 (B : nat) (m : nat) (n : nat) (x : nadd) : (term254 m B n x) = (term255 B m n x).
Proof. exact (@lem1264096 (Nat.mul B n) (term236 m n x) (term126 n x)). Qed.
Lemma lem1264107 (B : nat) (m : nat) (n : nat) : (term235 B m n) = (term235 B m n).
Proof. exact (eq_refl (term235 B m n)). Qed.
Lemma lem1264108 (B : nat) (m : nat) (n : nat) (x : nadd) : (term253 m B n x) = (term256 B m n x).
Proof. exact (MK_COMB (@lem1264107 B m n) (@lem1264097 B m n x)). Qed.
Lemma lem1264110 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1264111 (B : nat) (m : nat) (n : nat) (x : nadd) : (term256 B m n x) = (term257 B m n x).
Proof. exact (@lem1264110 (Nat.mul B n) (term36 B m n) (term258 m n x)). Qed.
Lemma lem1264127 (B : nat) (m : nat) (n : nat) (x : nadd) : (term253 m B n x) = (term257 B m n x).
Proof. exact (TRANS (@lem1264108 B m n x) (@lem1264111 B m n x)). Qed.
Lemma lem1264128 (B : nat) (m : nat) (n : nat) (x : nadd) : (term242 m B n x) = (term257 B m n x).
Proof. exact (TRANS (@lem1264088 m B n x) (@lem1264127 B m n x)). Qed.
Lemma lem1264129 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1264130 (B : nat) (m : nat) (n : nat) (x : nadd) : (term244 m B n x) = (term259 B m n x).
Proof. exact (MK_COMB (@lem1264129) (@lem1264128 B m n x)). Qed.
Lemma lem1264132 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1264133 (B : nat) (m : nat) (n : nat) (x : nadd) : (term256 B m n x) = (term257 B m n x).
Proof. exact (@lem1264132 (Nat.mul B n) (term36 B m n) (term258 m n x)). Qed.
Lemma lem1264149 (B : nat) (m : nat) (n : nat) (x : nadd) : ((term242 m B n x) = (term256 B m n x)) = ((term257 B m n x) = (term257 B m n x)).
Proof. exact (MK_COMB (@lem1264130 B m n x) (@lem1264133 B m n x)). Qed.
Lemma lem1264151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1264152 (x : nat) : (x = x) = True.
Proof. exact (@lem1264151 nat x). Qed.
Lemma lem1264153 (B : nat) (m : nat) (n : nat) (x : nadd) : ((term257 B m n x) = (term257 B m n x)) = True.
Proof. exact (@lem1264152 (term257 B m n x)). Qed.
Lemma lem1264154 (B : nat) (m : nat) (n : nat) (x : nadd) : ((term242 m B n x) = (term256 B m n x)) = True.
Proof. exact (TRANS (@lem1264149 B m n x) (@lem1264153 B m n x)). Qed.
Lemma lem1264155 (B : nat) (m : nat) (n : nat) (x : nadd) : True = ((term242 m B n x) = (term256 B m n x)).
Proof. exact (SYM (@lem1264154 B m n x)). Qed.
Lemma lem1264156 (B : nat) (m : nat) (n : nat) (x : nadd) : (term242 m B n x) = (term256 B m n x).
Proof. exact (EQ_MP (@lem1264155 B m n x) (@lem0)). Qed.
Lemma lem1264160 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (term144 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1264161 (B : nat) (m : nat) (n : nat) (d : nat) : (term249 B m n d) = (term260 B m n d).
Proof. exact (@lem1264160 (Nat.mul B n) (term36 B m n) d). Qed.
Lemma lem1264169 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1264170 (d : nat) (B : nat) (m : nat) (n : nat) : (term261 B m n d) = (term262 d B m n).
Proof. exact (@lem1264169 d (term36 B m n)). Qed.
Lemma lem1264174 (B : nat) (n : nat) : (term134 B n) = (term134 B n).
Proof. exact (eq_refl (term134 B n)). Qed.
Lemma lem1264175 (d : nat) (B : nat) (m : nat) (n : nat) : (term260 B m n d) = (term263 d B m n).
Proof. exact (MK_COMB (@lem1264174 B n) (@lem1264170 d B m n)). Qed.
Lemma lem1264177 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1264178 (d : nat) (B : nat) (m : nat) (n : nat) : (term263 d B m n) = (term264 d B m n).
Proof. exact (@lem1264177 d (Nat.mul B n) (term36 B m n)). Qed.
Lemma lem1264188 (d : nat) (B : nat) (m : nat) (n : nat) : (term260 B m n d) = (term264 d B m n).
Proof. exact (TRANS (@lem1264175 d B m n) (@lem1264178 d B m n)). Qed.
Lemma lem1264189 (d : nat) (B : nat) (m : nat) (n : nat) : (term249 B m n d) = (term264 d B m n).
Proof. exact (TRANS (@lem1264161 B m n d) (@lem1264188 d B m n)). Qed.
Lemma lem1264190 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1264191 (d : nat) (B : nat) (m : nat) (n : nat) : (term265 B m n d) = (term266 d B m n).
Proof. exact (MK_COMB (@lem1264190) (@lem1264189 d B m n)). Qed.
Lemma lem1264193 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1264194 (B : nat) (m : nat) (n : nat) (d : nat) : (term267 m B n d) = (term260 B m n d).
Proof. exact (@lem1264193 (Nat.mul B n) (term36 B m n) d). Qed.
Lemma lem1264202 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1264203 (d : nat) (B : nat) (m : nat) (n : nat) : (term261 B m n d) = (term262 d B m n).
Proof. exact (@lem1264202 d (term36 B m n)). Qed.
Lemma lem1264207 (B : nat) (n : nat) : (term134 B n) = (term134 B n).
Proof. exact (eq_refl (term134 B n)). Qed.
Lemma lem1264208 (d : nat) (B : nat) (m : nat) (n : nat) : (term260 B m n d) = (term263 d B m n).
Proof. exact (MK_COMB (@lem1264207 B n) (@lem1264203 d B m n)). Qed.
Lemma lem1264210 (n : nat) (m : nat) (p : nat) : (term144 m n p) = (term144 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1264211 (d : nat) (B : nat) (m : nat) (n : nat) : (term263 d B m n) = (term264 d B m n).
Proof. exact (@lem1264210 d (Nat.mul B n) (term36 B m n)). Qed.
Lemma lem1264221 (d : nat) (B : nat) (m : nat) (n : nat) : (term260 B m n d) = (term264 d B m n).
Proof. exact (TRANS (@lem1264208 d B m n) (@lem1264211 d B m n)). Qed.
Lemma lem1264222 (d : nat) (B : nat) (m : nat) (n : nat) : (term267 m B n d) = (term264 d B m n).
Proof. exact (TRANS (@lem1264194 B m n d) (@lem1264221 d B m n)). Qed.
Lemma lem1264223 (d : nat) (B : nat) (m : nat) (n : nat) : ((term249 B m n d) = (term267 m B n d)) = ((term264 d B m n) = (term264 d B m n)).
Proof. exact (MK_COMB (@lem1264191 d B m n) (@lem1264222 d B m n)). Qed.
Lemma lem1264225 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1264226 (x : nat) : (x = x) = True.
Proof. exact (@lem1264225 nat x). Qed.
Lemma lem1264227 (d : nat) (B : nat) (m : nat) (n : nat) : ((term264 d B m n) = (term264 d B m n)) = True.
Proof. exact (@lem1264226 (term264 d B m n)). Qed.
Lemma lem1264228 (m : nat) (B : nat) (n : nat) (d : nat) : ((term249 B m n d) = (term267 m B n d)) = True.
Proof. exact (TRANS (@lem1264223 d B m n) (@lem1264227 d B m n)). Qed.
Lemma lem1264229 (m : nat) (B : nat) (n : nat) (d : nat) : True = ((term249 B m n d) = (term267 m B n d)).
Proof. exact (SYM (@lem1264228 m B n d)). Qed.
Lemma lem1264230 (m : nat) (B : nat) (n : nat) (d : nat) : (term249 B m n d) = (term267 m B n d).
Proof. exact (EQ_MP (@lem1264229 m B n d) (@lem0)). Qed.
Lemma lem1264231 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1264232 (B : nat) (m : nat) (n : nat) (x : nadd) : (term244 m B n x) = (term268 B m n x).
Proof. exact (MK_COMB (@lem1264231) (@lem1264156 B m n x)). Qed.
Lemma lem1264233 (x : nadd) (m : nat) (B : nat) (n : nat) (d : nat) : ((term242 m B n x) = (term249 B m n d)) = ((term256 B m n x) = (term267 m B n d)).
Proof. exact (MK_COMB (@lem1264232 B m n x) (@lem1264230 m B n d)). Qed.
Lemma lem1264246 (m : nat) : term173 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1264247 (m : nat) : (term173 m) = (term174 m).
Proof. exact (eq_refl (term173 m)). Qed.
Lemma lem1264248 (m : nat) : term174 m.
Proof. exact (EQ_MP (@lem1264247 m) (@lem1264246 m)). Qed.
Lemma lem1264249 (m : nat) (n : nat) : term175 m n.
Proof. exact (@lem1264248 m n). Qed.
Lemma lem1264250 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (eq_refl (term175 m n)). Qed.
Lemma lem1264251 (m : nat) (n : nat) : term176 m n.
Proof. exact (EQ_MP (@lem1264250 m n) (@lem1264249 m n)). Qed.
Lemma lem1264252 (m : nat) (n : nat) (p : nat) : term177 m n p.
Proof. exact (@lem1264251 m n p). Qed.
Lemma lem1264253 (m : nat) (n : nat) (p : nat) : (term177 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term177 m n p)). Qed.
Lemma lem1264256 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1264253 m n p) (@lem1264252 m n p)). Qed.
Lemma lem1264257 (m : nat) (x : nadd) (B : nat) (n : nat) (d : nat) : ((term256 B m n x) = (term267 m B n d)) = ((term255 B m n x) = (term269 B n d)).
Proof. exact (@lem1264256 (term36 B m n) (term255 B m n x) (term269 B n d)). Qed.
Lemma lem1264259 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1264253 m n p) (@lem1264252 m n p)). Qed.
Lemma lem1264264 (B : nat) (m : nat) (n : nat) (x : nadd) (d : nat) : ((term255 B m n x) = (term269 B n d)) = ((term258 m n x) = d).
Proof. exact (@lem1264259 (Nat.mul B n) (term258 m n x) d). Qed.
Lemma lem1264265 (B : nat) (m : nat) (n : nat) (x : nadd) (d : nat) : ((term256 B m n x) = (term267 m B n d)) = ((term258 m n x) = d).
Proof. exact (TRANS (@lem1264257 m x B n d) (@lem1264264 B m n x d)). Qed.
Lemma lem1264266 (x : nadd) (B : nat) (m : nat) (n : nat) (d : nat) : (term270 x B m n d) = (term270 x B m n d).
Proof. exact (eq_refl (term270 x B m n d)). Qed.
Lemma lem1264267 (B : nat) (m : nat) (n : nat) (x : nadd) (d : nat) : (((term242 m B n x) = (term249 B m n d)) = ((term256 B m n x) = (term267 m B n d))) = (((term242 m B n x) = (term249 B m n d)) = ((term258 m n x) = d)).
Proof. exact (MK_COMB (@lem1264266 x B m n d) (@lem1264265 B m n x d)). Qed.
Lemma lem1264268 (B : nat) (m : nat) (n : nat) (x : nadd) (d : nat) : ((term242 m B n x) = (term249 B m n d)) = ((term258 m n x) = d).
Proof. exact (EQ_MP (@lem1264267 B m n x d) (@lem1264233 x m B n d)). Qed.
Lemma lem1264269 (B : nat) (m : nat) (n : nat) (x : nadd) : (term251 x B m n) = (term271 m n x).
Proof. exact (fun_ext (fun d : nat => @lem1264268 B m n x d)). Qed.
Lemma lem1264270 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1264271 (B : nat) (m : nat) (n : nat) (x : nadd) : (term252 x B m n) = (term272 m n x).
Proof. exact (MK_COMB (@lem1264270) (@lem1264269 B m n x)). Qed.
Lemma lem1264272 (x : nadd) (B : nat) (m : nat) (n : nat) : (term272 m n x) = (term252 x B m n).
Proof. exact (SYM (@lem1264271 B m n x)). Qed.
Lemma lem1264274 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem1263178 A a) (@lem1263177 A a)). Qed.
Lemma lem1264275 (a : nat) : (term184 a) = True.
Proof. exact (@lem1264274 nat a). Qed.
Lemma lem1264276 (m : nat) (n : nat) (x : nadd) : (term272 m n x) = True.
Proof. exact (@lem1264275 (term258 m n x)). Qed.
Lemma lem1264277 (m : nat) (n : nat) (x : nadd) : True = (term272 m n x).
Proof. exact (SYM (@lem1264276 m n x)). Qed.
Lemma lem1264278 (m : nat) (n : nat) (x : nadd) : term272 m n x.
Proof. exact (EQ_MP (@lem1264277 m n x) (@lem0)). Qed.
Lemma lem1264279 (x : nadd) (B : nat) (m : nat) (n : nat) : term252 x B m n.
Proof. exact (EQ_MP (@lem1264272 x B m n) (@lem1264278 m n x)). Qed.
Lemma lem1264280 (n : nat) (m : nat) (B : nat) (x : nadd) : term228 n m B x.
Proof. exact (EQ_MP (@lem1264083 n m B x) (@lem1264279 x B m n)). Qed.
Lemma lem1264281 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term209 n m B x.
Proof. exact (@lem1263952 n m x B h1 (@lem1264280 n m B x)). Qed.
Lemma lem1264282 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term203 n m B x.
Proof. exact (EQ_MP (@lem1263883 n m B x) (@lem1264281 n m x B h1)). Qed.
Lemma lem1264283 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term195 n m B x.
Proof. exact (EQ_MP (@lem1263867 n m B x) (@lem1264282 n m x B h1)). Qed.
Lemma lem1264284 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term186 n m B x.
Proof. exact (EQ_MP (@lem1263855 n m B x) (@lem1264283 n m x B h1)). Qed.
Lemma lem1264285 (m : nat) (x : nadd) (B : nat) (n : nat) (h1 : term114 x B) (h2 : term111 n) : term185 n m B x.
Proof. exact (@lem1264284 n m x B h1 (@lem1263459 n h2)). Qed.
Lemma lem1264286 (n : nat) (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term185 n m B x.
Proof. exact (or_elim (@lem1263457 n) (fun h0 : n = (NUMERAL 0) => @lem1263839 m B x n h0) (fun h0 : term111 n => @lem1264285 m x B n h1 h0)). Qed.
Lemma lem1264291 (m : nat) (x : nadd) (B : nat) (h1 : term114 x B) : term273 m B x.
Proof. exact (fun n : nat => @lem1264286 n m x B h1). Qed.
Lemma lem1264296 (x : nadd) (B : nat) (h1 : term114 x B) : term274 B x.
Proof. exact (fun m : nat => @lem1264291 m x B h1). Qed.
Lemma lem1264297 (x : nadd) (B : nat) (h1 : term114 x B) : term275 x.
Proof. exact (ex_intro (term276 x) (term138 B x) (@lem1264296 x B h1)). Qed.
Lemma lem1264298 (x : nadd) : term275 x.
Proof. exact (ex_elim (@lem1263462 x) (fun B : nat => fun h0 : term277 x B => @lem1264297 x B h0)). Qed.
Lemma lem1264303 : term278.
Proof. exact (fun x : nadd => @lem1264298 x). Qed.
