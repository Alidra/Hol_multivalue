Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_CROSS_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4334204 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4334205 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4334206 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4334205 _103718 _103721 x) (@lem4334204 _103718 _103721 x)). Qed.
Lemma lem4334207 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4334206 _103718 _103721 x y). Qed.
Lemma lem4334208 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4334209 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4334208 _103718 _103721 x y) (@lem4334207 _103718 _103721 x y)). Qed.
Lemma lem4334210 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4334209 _103718 _103721 x y s). Qed.
Lemma lem4334211 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4334212 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4334211 _103718 _103721 x s y) (@lem4334210 _103718 _103721 x y s)). Qed.
Lemma lem4334213 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4334212 _103718 _103721 x s y t). Qed.
Lemma lem4334214 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4334216 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term9 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4334217 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term9 _5106 _5107 P) = ((term10 _5106 _5107 P) = (term11 _5106 _5107 P)).
Proof. exact (eq_refl (term9 _5106 _5107 P)). Qed.
Lemma lem4334244 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = (term11 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4334217 _5106 _5107 P) (@lem4334216 _5106 _5107 P)). Qed.
Lemma lem4334245 {_104099 _104100 : Type'} (P : type1223 _104099 _104100) : (term10 _104099 _104100 P) = (term11 _104099 _104100 P).
Proof. exact (@lem4334244 _104099 _104100 P). Qed.
Lemma lem4334246 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term12 _104099 _104100 s t P) = (term13 _104099 _104100 s t P).
Proof. exact (@lem4334245 _104099 _104100 (term14 _104099 _104100 s t P)). Qed.
Lemma lem4334247 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (z : prod _104100 _104099) : (term15 _104099 _104100 s t P z) = (term16 _104099 _104100 s t P z).
Proof. exact (eq_refl (term15 _104099 _104100 s t P z)). Qed.
Lemma lem4334248 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term17 _104099 _104100 s t P) = (term14 _104099 _104100 s t P).
Proof. exact (fun_ext (fun z : prod _104100 _104099 => @lem4334247 _104099 _104100 s t P z)). Qed.
Lemma lem4334249 {_104099 _104100 : Type'} : (@all (prod _104100 _104099)) = (@all (prod _104100 _104099)).
Proof. exact (eq_refl (@all (prod _104100 _104099))). Qed.
Lemma lem4334250 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term12 _104099 _104100 s t P) = (term18 _104099 _104100 s t P).
Proof. exact (MK_COMB (@lem4334249 _104099 _104100) (@lem4334248 _104099 _104100 s t P)). Qed.
Lemma lem4334251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334252 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term19 _104099 _104100 s t P) = (term20 _104099 _104100 s t P).
Proof. exact (MK_COMB (@lem4334251) (@lem4334250 _104099 _104100 s t P)). Qed.
Lemma lem4334253 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (p1 : _104100) (p2 : _104099) : (term21 _104099 _104100 s t P p1 p2) = (term22 _104099 _104100 s t P p1 p2).
Proof. exact (eq_refl (term21 _104099 _104100 s t P p1 p2)). Qed.
Lemma lem4334254 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (p1 : _104100) : (term23 _104099 _104100 s t P p1) = (term24 _104099 _104100 s t P p1).
Proof. exact (fun_ext (fun p2 : _104099 => @lem4334253 _104099 _104100 s t P p1 p2)). Qed.
Lemma lem4334255 {_104099 : Type'} : (@all _104099) = (@all _104099).
Proof. exact (eq_refl (@all _104099)). Qed.
Lemma lem4334256 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (p1 : _104100) : (term25 _104099 _104100 s t P p1) = (term26 _104099 _104100 s t P p1).
Proof. exact (MK_COMB (@lem4334255 _104099) (@lem4334254 _104099 _104100 s t P p1)). Qed.
Lemma lem4334257 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term27 _104099 _104100 s t P) = (term28 _104099 _104100 s t P).
Proof. exact (fun_ext (fun p1 : _104100 => @lem4334256 _104099 _104100 s t P p1)). Qed.
Lemma lem4334258 {_104100 : Type'} : (@all _104100) = (@all _104100).
Proof. exact (eq_refl (@all _104100)). Qed.
Lemma lem4334259 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term13 _104099 _104100 s t P) = (term29 _104099 _104100 s t P).
Proof. exact (MK_COMB (@lem4334258 _104100) (@lem4334257 _104099 _104100 s t P)). Qed.
Lemma lem4334260 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term12 _104099 _104100 s t P) = (term13 _104099 _104100 s t P)) = ((term18 _104099 _104100 s t P) = (term29 _104099 _104100 s t P)).
Proof. exact (MK_COMB (@lem4334252 _104099 _104100 s t P) (@lem4334259 _104099 _104100 s t P)). Qed.
Lemma lem4334261 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term18 _104099 _104100 s t P) = (term29 _104099 _104100 s t P).
Proof. exact (EQ_MP (@lem4334260 _104099 _104100 s t P) (@lem4334246 _104099 _104100 s t P)). Qed.
Lemma lem4334277 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4334214 _103718 _103721 x s y t) (@lem4334213 _103718 _103721 x s y t)). Qed.
Lemma lem4334278 {_104099 _104100 : Type'} (x : _104100) (s : _104100 -> Prop) (y : _104099) (t : _104099 -> Prop) : (term30 _104099 _104100 x y s t) = (term31 _104099 _104100 x s y t).
Proof. exact (@lem4334277 _104100 _104099 x s y t). Qed.
Lemma lem4334279 {_104099 _104100 : Type'} (p1 : _104100) (s : _104100 -> Prop) (p2 : _104099) (t : _104099 -> Prop) : (term30 _104099 _104100 p1 p2 s t) = (term31 _104099 _104100 p1 s p2 t).
Proof. exact (@lem4334278 _104099 _104100 p1 s p2 t). Qed.
Lemma lem4334282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4334283 {_104099 _104100 : Type'} (p1 : _104100) (s : _104100 -> Prop) (p2 : _104099) (t : _104099 -> Prop) : (term32 _104099 _104100 p1 p2 s t) = (term33 _104099 _104100 p1 s p2 t).
Proof. exact (MK_COMB (@lem4334282) (@lem4334279 _104099 _104100 p1 s p2 t)). Qed.
Lemma lem4334284 {_104099 _104100 : Type'} (P : type1223 _104099 _104100) (p1 : _104100) (p2 : _104099) : (term34 _104099 _104100 P p1 p2) = (term34 _104099 _104100 P p1 p2).
Proof. exact (eq_refl (term34 _104099 _104100 P p1 p2)). Qed.
Lemma lem4334285 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (p1 : _104100) (p2 : _104099) : (term22 _104099 _104100 s t P p1 p2) = (term35 _104099 _104100 s t P p1 p2).
Proof. exact (MK_COMB (@lem4334283 _104099 _104100 p1 s p2 t) (@lem4334284 _104099 _104100 P p1 p2)). Qed.
Lemma lem4334288 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (p1 : _104100) : (term24 _104099 _104100 s t P p1) = (term36 _104099 _104100 s t P p1).
Proof. exact (fun_ext (fun p2 : _104099 => @lem4334285 _104099 _104100 s t P p1 p2)). Qed.
Lemma lem4334289 {_104099 : Type'} : (@all _104099) = (@all _104099).
Proof. exact (eq_refl (@all _104099)). Qed.
Lemma lem4334290 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) (p1 : _104100) : (term26 _104099 _104100 s t P p1) = (term37 _104099 _104100 s t P p1).
Proof. exact (MK_COMB (@lem4334289 _104099) (@lem4334288 _104099 _104100 s t P p1)). Qed.
Lemma lem4334297 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term28 _104099 _104100 s t P) = (term38 _104099 _104100 s t P).
Proof. exact (fun_ext (fun p1 : _104100 => @lem4334290 _104099 _104100 s t P p1)). Qed.
Lemma lem4334298 {_104100 : Type'} : (@all _104100) = (@all _104100).
Proof. exact (eq_refl (@all _104100)). Qed.
Lemma lem4334299 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term29 _104099 _104100 s t P) = (term39 _104099 _104100 s t P).
Proof. exact (MK_COMB (@lem4334298 _104100) (@lem4334297 _104099 _104100 s t P)). Qed.
Lemma lem4334306 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term18 _104099 _104100 s t P) = (term39 _104099 _104100 s t P).
Proof. exact (TRANS (@lem4334261 _104099 _104100 s t P) (@lem4334299 _104099 _104100 s t P)). Qed.
Lemma lem4334307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334308 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term20 _104099 _104100 s t P) = (term40 _104099 _104100 s t P).
Proof. exact (MK_COMB (@lem4334307) (@lem4334306 _104099 _104100 s t P)). Qed.
Lemma lem4334325 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P).
Proof. exact (eq_refl (term39 _104099 _104100 s t P)). Qed.
Lemma lem4334326 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term18 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = ((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)).
Proof. exact (MK_COMB (@lem4334308 _104099 _104100 s t P) (@lem4334325 _104099 _104100 s t P)). Qed.
Lemma lem4334328 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4334329 (x : Prop) : (x = x) = True.
Proof. exact (@lem4334328 Prop x). Qed.
Lemma lem4334330 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True.
Proof. exact (@lem4334329 (term39 _104099 _104100 s t P)). Qed.
Lemma lem4334333 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term41 _104099 _104100 s t P) = (term41 _104099 _104100 s t P).
Proof. exact (eq_refl (term41 _104099 _104100 s t P)). Qed.
Lemma lem4334334 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term41 _104099 _104100 s t P) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True).
Proof. exact (eq_refl (term41 _104099 _104100 s t P)). Qed.
Lemma lem4334335 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term42 _104099 _104100 s t P) = (term42 _104099 _104100 s t P).
Proof. exact (eq_refl (term42 _104099 _104100 s t P)). Qed.
Lemma lem4334336 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term41 _104099 _104100 s t P) = (term41 _104099 _104100 s t P)) = ((term41 _104099 _104100 s t P) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True)).
Proof. exact (MK_COMB (@lem4334335 _104099 _104100 s t P) (@lem4334334 _104099 _104100 s t P)). Qed.
Lemma lem4334337 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term41 _104099 _104100 s t P) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True).
Proof. exact (eq_refl (term41 _104099 _104100 s t P)). Qed.
Lemma lem4334338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334339 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (term42 _104099 _104100 s t P) = (term43 _104099 _104100 s t P).
Proof. exact (MK_COMB (@lem4334338) (@lem4334337 _104099 _104100 s t P)). Qed.
Lemma lem4334340 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True).
Proof. exact (eq_refl (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True)). Qed.
Lemma lem4334341 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term41 _104099 _104100 s t P) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True)) = ((((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True)).
Proof. exact (MK_COMB (@lem4334339 _104099 _104100 s t P) (@lem4334340 _104099 _104100 s t P)). Qed.
Lemma lem4334342 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term41 _104099 _104100 s t P) = (term41 _104099 _104100 s t P)) = ((((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True)).
Proof. exact (TRANS (@lem4334336 _104099 _104100 s t P) (@lem4334341 _104099 _104100 s t P)). Qed.
Lemma lem4334343 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True) = (((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True).
Proof. exact (EQ_MP (@lem4334342 _104099 _104100 s t P) (@lem4334333 _104099 _104100 s t P)). Qed.
Lemma lem4334344 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term39 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True.
Proof. exact (EQ_MP (@lem4334343 _104099 _104100 s t P) (@lem4334330 _104099 _104100 s t P)). Qed.
Lemma lem4334345 {_104099 _104100 : Type'} (s : _104100 -> Prop) (t : _104099 -> Prop) (P : type1223 _104099 _104100) : ((term18 _104099 _104100 s t P) = (term39 _104099 _104100 s t P)) = True.
Proof. exact (TRANS (@lem4334326 _104099 _104100 s t P) (@lem4334344 _104099 _104100 s t P)). Qed.
Lemma lem4334346 {_104099 _104100 : Type'} (s : _104100 -> Prop) (P : type1223 _104099 _104100) : (term44 _104099 _104100 s P) = (term45 _104099).
Proof. exact (fun_ext (fun t : _104099 -> Prop => @lem4334345 _104099 _104100 s t P)). Qed.
Lemma lem4334347 {_104099 : Type'} : (@all (_104099 -> Prop)) = (@all (_104099 -> Prop)).
Proof. exact (eq_refl (@all (_104099 -> Prop))). Qed.
Lemma lem4334348 {_104099 _104100 : Type'} (s : _104100 -> Prop) (P : type1223 _104099 _104100) : (term46 _104099 _104100 s P) = (term47 _104099).
Proof. exact (MK_COMB (@lem4334347 _104099) (@lem4334346 _104099 _104100 s P)). Qed.
Lemma lem4334350 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4334351 {_104099 : Type'} (t : Prop) : (term49 _104099 t) = t.
Proof. exact (@lem4334350 (_104099 -> Prop) t). Qed.
Lemma lem4334352 {_104099 : Type'} : (term47 _104099) = True.
Proof. exact (@lem4334351 _104099 True). Qed.
Lemma lem4334353 {_104099 _104100 : Type'} (s : _104100 -> Prop) (P : type1223 _104099 _104100) : (term46 _104099 _104100 s P) = True.
Proof. exact (TRANS (@lem4334348 _104099 _104100 s P) (@lem4334352 _104099)). Qed.
Lemma lem4334354 {_104099 _104100 : Type'} (P : type1223 _104099 _104100) : (term50 _104099 _104100 P) = (term45 _104100).
Proof. exact (fun_ext (fun s : _104100 -> Prop => @lem4334353 _104099 _104100 s P)). Qed.
Lemma lem4334355 {_104100 : Type'} : (@all (_104100 -> Prop)) = (@all (_104100 -> Prop)).
Proof. exact (eq_refl (@all (_104100 -> Prop))). Qed.
Lemma lem4334356 {_104099 _104100 : Type'} (P : type1223 _104099 _104100) : (term51 _104099 _104100 P) = (term47 _104100).
Proof. exact (MK_COMB (@lem4334355 _104100) (@lem4334354 _104099 _104100 P)). Qed.
Lemma lem4334358 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4334359 {_104100 : Type'} (t : Prop) : (term49 _104100 t) = t.
Proof. exact (@lem4334358 (_104100 -> Prop) t). Qed.
Lemma lem4334360 {_104100 : Type'} : (term47 _104100) = True.
Proof. exact (@lem4334359 _104100 True). Qed.
Lemma lem4334361 {_104099 _104100 : Type'} (P : type1223 _104099 _104100) : (term51 _104099 _104100 P) = True.
Proof. exact (TRANS (@lem4334356 _104099 _104100 P) (@lem4334360 _104100)). Qed.
Lemma lem4334362 {_104099 _104100 : Type'} : (term52 _104099 _104100) = (term53 _104099 _104100).
Proof. exact (fun_ext (fun P : type1223 _104099 _104100 => @lem4334361 _104099 _104100 P)). Qed.
Lemma lem4334363 {_104099 _104100 : Type'} : (@all ((prod _104100 _104099) -> Prop)) = (@all ((prod _104100 _104099) -> Prop)).
Proof. exact (eq_refl (@all ((prod _104100 _104099) -> Prop))). Qed.
Lemma lem4334364 {_104099 _104100 : Type'} : (term54 _104099 _104100) = (term55 _104099 _104100).
Proof. exact (MK_COMB (@lem4334363 _104099 _104100) (@lem4334362 _104099 _104100)). Qed.
Lemma lem4334366 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4334367 {_104099 _104100 : Type'} (t : Prop) : (term56 _104099 _104100 t) = t.
Proof. exact (@lem4334366 (type1223 _104099 _104100) t). Qed.
Lemma lem4334368 {_104099 _104100 : Type'} : (term55 _104099 _104100) = True.
Proof. exact (@lem4334367 _104099 _104100 True). Qed.
Lemma lem4334369 {_104099 _104100 : Type'} : (term54 _104099 _104100) = True.
Proof. exact (TRANS (@lem4334364 _104099 _104100) (@lem4334368 _104099 _104100)). Qed.
Lemma lem4334370 {_104099 _104100 : Type'} : True = (term54 _104099 _104100).
Proof. exact (SYM (@lem4334369 _104099 _104100)). Qed.
Lemma lem4334371 {_104099 _104100 : Type'} : term54 _104099 _104100.
Proof. exact (EQ_MP (@lem4334370 _104099 _104100) (@lem0)). Qed.
