Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_CONG_RREM_term_abbrevs.
Require Import INT_REM_EQ_spec.
Require Import INT_REM_REM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2528205 (m : int) (n : int) (p : int) (h1 : ((rem m p) = (rem n p)) = (term0 m n p)) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem2528206 (m : int) (n : int) (p : int) (h1 : ((rem m p) = (rem n p)) = (term0 m n p)) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (SYM (@lem2528205 m n p h1)). Qed.
Lemma lem2528207 (m : int) (n : int) (p : int) (h1 : (term0 m n p) = ((rem m p) = (rem n p))) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (h1). Qed.
Lemma lem2528208 (m : int) (n : int) (p : int) (h1 : (term0 m n p) = ((rem m p) = (rem n p))) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (SYM (@lem2528207 m n p h1)). Qed.
Lemma lem2528209 (m : int) (n : int) (p : int) : (((rem m p) = (rem n p)) = (term0 m n p)) = ((term0 m n p) = ((rem m p) = (rem n p))).
Proof. exact (prop_ext (fun h1 : ((rem m p) = (rem n p)) = (term0 m n p) => @lem2528206 m n p h1) (fun h1 : (term0 m n p) = ((rem m p) = (rem n p)) => @lem2528208 m n p h1)). Qed.
Lemma lem2528210 (m : int) (n : int) : (term1 m n) = (term2 m n).
Proof. exact (fun_ext (fun p : int => @lem2528209 m n p)). Qed.
Lemma lem2528211 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528212 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem2528211) (@lem2528210 m n)). Qed.
Lemma lem2528213 (m : int) : (term5 m) = (term6 m).
Proof. exact (fun_ext (fun n : int => @lem2528212 m n)). Qed.
Lemma lem2528214 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528215 (m : int) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem2528214) (@lem2528213 m)). Qed.
Lemma lem2528216 : term9 = term10.
Proof. exact (fun_ext (fun m : int => @lem2528215 m)). Qed.
Lemma lem2528217 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528218 : term11 = term12.
Proof. exact (MK_COMB (@lem2528217) (@lem2528216)). Qed.
Lemma lem2528219 : term12.
Proof. exact (EQ_MP (@lem2528218) (@lem2522863)). Qed.
Lemma lem2528220 (m : int) : term13 m.
Proof. exact (@lem2521244 m). Qed.
Lemma lem2528221 (m : int) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2528222 (m : int) : term14 m.
Proof. exact (EQ_MP (@lem2528221 m) (@lem2528220 m)). Qed.
Lemma lem2528223 (m : int) (n : int) : term15 m n.
Proof. exact (@lem2528222 m n). Qed.
Lemma lem2528224 (m : int) (n : int) : (term15 m n) = ((term16 m n) = (rem m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem2528226 (m : int) : term17 m.
Proof. exact (@lem2528219 m). Qed.
Lemma lem2528227 (m : int) : (term17 m) = (term8 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem2528228 (m : int) : term8 m.
Proof. exact (EQ_MP (@lem2528227 m) (@lem2528226 m)). Qed.
Lemma lem2528229 (m : int) (n : int) : term18 m n.
Proof. exact (@lem2528228 m n). Qed.
Lemma lem2528230 (m : int) (n : int) : (term18 m n) = (term4 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2528231 (m : int) (n : int) : term4 m n.
Proof. exact (EQ_MP (@lem2528230 m n) (@lem2528229 m n)). Qed.
Lemma lem2528232 (m : int) (n : int) (p : int) : term19 m n p.
Proof. exact (@lem2528231 m n p). Qed.
Lemma lem2528233 (m : int) (n : int) (p : int) : (term19 m n p) = ((term0 m n p) = ((rem m p) = (rem n p))).
Proof. exact (eq_refl (term19 m n p)). Qed.
Lemma lem2528250 (m : int) (n : int) (p : int) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (EQ_MP (@lem2528233 m n p) (@lem2528232 m n p)). Qed.
Lemma lem2528251 (x : int) (y : int) (n : int) : (term20 x y n) = ((rem x n) = (term16 y n)).
Proof. exact (@lem2528250 x (rem y n) n). Qed.
Lemma lem2528255 (m : int) (n : int) : (term16 m n) = (rem m n).
Proof. exact (EQ_MP (@lem2528224 m n) (@lem2528223 m n)). Qed.
Lemma lem2528256 (y : int) (n : int) : (term16 y n) = (rem y n).
Proof. exact (@lem2528255 y n). Qed.
Lemma lem2528257 (x : int) (n : int) : (term21 x n) = (term21 x n).
Proof. exact (eq_refl (term21 x n)). Qed.
Lemma lem2528258 (x : int) (y : int) (n : int) : ((rem x n) = (term16 y n)) = ((rem x n) = (rem y n)).
Proof. exact (MK_COMB (@lem2528257 x n) (@lem2528256 y n)). Qed.
Lemma lem2528261 (x : int) (y : int) (n : int) : (term20 x y n) = ((rem x n) = (rem y n)).
Proof. exact (TRANS (@lem2528251 x y n) (@lem2528258 x y n)). Qed.
Lemma lem2528262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2528263 (x : int) (y : int) (n : int) : (term22 x y n) = (term23 x y n).
Proof. exact (MK_COMB (@lem2528262) (@lem2528261 x y n)). Qed.
Lemma lem2528265 (m : int) (n : int) (p : int) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (EQ_MP (@lem2528233 m n p) (@lem2528232 m n p)). Qed.
Lemma lem2528266 (x : int) (y : int) (n : int) : (term0 x y n) = ((rem x n) = (rem y n)).
Proof. exact (@lem2528265 x y n). Qed.
Lemma lem2528269 (x : int) (y : int) (n : int) : ((term20 x y n) = (term0 x y n)) = (((rem x n) = (rem y n)) = ((rem x n) = (rem y n))).
Proof. exact (MK_COMB (@lem2528263 x y n) (@lem2528266 x y n)). Qed.
Lemma lem2528271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2528272 (x : Prop) : (x = x) = True.
Proof. exact (@lem2528271 Prop x). Qed.
Lemma lem2528273 (x : int) (y : int) (n : int) : (((rem x n) = (rem y n)) = ((rem x n) = (rem y n))) = True.
Proof. exact (@lem2528272 ((rem x n) = (rem y n))). Qed.
Lemma lem2528274 (x : int) (y : int) (n : int) : ((term20 x y n) = (term0 x y n)) = True.
Proof. exact (TRANS (@lem2528269 x y n) (@lem2528273 x y n)). Qed.
Lemma lem2528275 (x : int) (y : int) : (term24 x y) = term25.
Proof. exact (fun_ext (fun n : int => @lem2528274 x y n)). Qed.
Lemma lem2528276 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528277 (x : int) (y : int) : (term26 x y) = term27.
Proof. exact (MK_COMB (@lem2528276) (@lem2528275 x y)). Qed.
Lemma lem2528279 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2528280 (t : Prop) : (term29 t) = t.
Proof. exact (@lem2528279 int t). Qed.
Lemma lem2528281 : term27 = True.
Proof. exact (@lem2528280 True). Qed.
Lemma lem2528282 (x : int) (y : int) : (term26 x y) = True.
Proof. exact (TRANS (@lem2528277 x y) (@lem2528281)). Qed.
Lemma lem2528283 (x : int) : (term30 x) = term25.
Proof. exact (fun_ext (fun y : int => @lem2528282 x y)). Qed.
Lemma lem2528284 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528285 (x : int) : (term31 x) = term27.
Proof. exact (MK_COMB (@lem2528284) (@lem2528283 x)). Qed.
Lemma lem2528287 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2528288 (t : Prop) : (term29 t) = t.
Proof. exact (@lem2528287 int t). Qed.
Lemma lem2528289 : term27 = True.
Proof. exact (@lem2528288 True). Qed.
Lemma lem2528290 (x : int) : (term31 x) = True.
Proof. exact (TRANS (@lem2528285 x) (@lem2528289)). Qed.
Lemma lem2528291 : term32 = term25.
Proof. exact (fun_ext (fun x : int => @lem2528290 x)). Qed.
Lemma lem2528292 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528293 : term33 = term27.
Proof. exact (MK_COMB (@lem2528292) (@lem2528291)). Qed.
Lemma lem2528295 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2528296 (t : Prop) : (term29 t) = t.
Proof. exact (@lem2528295 int t). Qed.
Lemma lem2528297 : term27 = True.
Proof. exact (@lem2528296 True). Qed.
Lemma lem2528298 : term33 = True.
Proof. exact (TRANS (@lem2528293) (@lem2528297)). Qed.
Lemma lem2528299 : True = term33.
Proof. exact (SYM (@lem2528298)). Qed.
Lemma lem2528300 : term33.
Proof. exact (EQ_MP (@lem2528299) (@lem0)). Qed.
