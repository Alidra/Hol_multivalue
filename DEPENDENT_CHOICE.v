Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DEPENDENT_CHOICE_term_abbrevs.
Require Import DEPENDENT_CHOICE_FIXED_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem297910 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem297911 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem297912 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem297911 t1) (@lem297910 t1)). Qed.
Lemma lem297913 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem297912 t1 t2). Qed.
Lemma lem297914 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem297915 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem297914 t1 t2) (@lem297913 t1 t2)). Qed.
Lemma lem297916 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem297915 t1 t2 t3). Qed.
Lemma lem297917 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem297918 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem297917 t1 t2 t3) (@lem297916 t1 t2 t3)). Qed.
Lemma lem297919 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem297918 t1 t2 t3)). Qed.
Lemma lem297921 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem297922 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem297921 (term8 A)). Qed.
Lemma lem297923 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem297922 A)). Qed.
Lemma lem297924 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem297927 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem297928 {A : Type'} : term12 A.
Proof. exact (fun h0 : term11 A => @lem297927 A h0). Qed.
Lemma lem297929 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem297930 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem297931 {A : Type'} (h1 : term11 A) (h2 : term12 A) : term11 A.
Proof. exact (@lem297929 A h2 (@lem297930 A h1)). Qed.
Lemma lem297932 {A : Type'} (h1 : term11 A) : term13 A.
Proof. exact (fun h0 : term12 A => @lem297931 A h1 h0). Qed.
Lemma lem297933 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem297934 {A : Type'} (h1 : term11 A) (h2 : term12 A) : term11 A.
Proof. exact (@lem297932 A h1 (@lem297933 A h2)). Qed.
Lemma lem297935 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (fun h0 : term11 A => @lem297934 A h0 h1). Qed.
Lemma lem297936 {A : Type'} : term14 A.
Proof. exact (fun h0 : term12 A => @lem297935 A h0). Qed.
Lemma lem297939 {A : Type'} : term12 A.
Proof. exact (@lem297936 A (@lem297928 A)). Qed.
Lemma lem297940 {A : Type'} : term12 A.
Proof. exact (@lem297939 A). Qed.
Lemma lem298078 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem298079 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (@lem298078 (term17 A)). Qed.
Lemma lem298216 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem298223 {A : Type'} : (term11 A) = (term19 A).
Proof. exact (MK_COMB (@lem298216 A) (@lem298079 A)). Qed.
Lemma lem298224 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term20 A R f n) = (term20 A R f n).
Proof. exact (eq_refl (term20 A R f n)). Qed.
Lemma lem298225 {A : Type'} (R : type1594 A) (f : nat -> A) : (term21 A R f) = (term21 A R f).
Proof. exact (fun_ext (fun n : nat => @lem298224 A R f n)). Qed.
Lemma lem298226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298227 {A : Type'} (R : type1594 A) (f : nat -> A) : (term22 A R f) = (term22 A R f).
Proof. exact (MK_COMB (@lem298226) (@lem298225 A R f)). Qed.
Lemma lem298228 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term23 A P f n) = (term23 A P f n).
Proof. exact (eq_refl (term23 A P f n)). Qed.
Lemma lem298229 {A : Type'} (P : type1597 A) (f : nat -> A) : (term24 A P f) = (term24 A P f).
Proof. exact (fun_ext (fun n : nat => @lem298228 A P f n)). Qed.
Lemma lem298230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298231 {A : Type'} (P : type1597 A) (f : nat -> A) : (term25 A P f) = (term25 A P f).
Proof. exact (MK_COMB (@lem298230) (@lem298229 A P f)). Qed.
Lemma lem298232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298233 {A : Type'} (P : type1597 A) (f : nat -> A) : (term26 A P f) = (term26 A P f).
Proof. exact (MK_COMB (@lem298232) (@lem298231 A P f)). Qed.
Lemma lem298234 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term27 A P R f) = (term27 A P R f).
Proof. exact (MK_COMB (@lem298233 A P f) (@lem298227 A R f)). Qed.
Lemma lem298237 {A : Type'} (f : nat -> A) (a : A) : (term28 A f a) = (term28 A f a).
Proof. exact (eq_refl (term28 A f a)). Qed.
Lemma lem298238 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term29 A a P R f) = (term29 A a P R f).
Proof. exact (MK_COMB (@lem298237 A f a) (@lem298234 A P R f)). Qed.
Lemma lem298239 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term30 A a P R) = (term30 A a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem298238 A a P R f)). Qed.
Lemma lem298240 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem298241 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (MK_COMB (@lem298240 A) (@lem298239 A a P R)). Qed.
Lemma lem298246 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term32 A P R n x y) = (term32 A P R n x y).
Proof. exact (eq_refl (term32 A P R n x y)). Qed.
Lemma lem298247 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term33 A P R n x) = (term33 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem298246 A P R n x y)). Qed.
Lemma lem298248 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298249 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term34 A P R n x) = (term34 A P R n x).
Proof. exact (MK_COMB (@lem298248 A) (@lem298247 A P R n x)). Qed.
Lemma lem298252 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term35 A P n x) = (term35 A P n x).
Proof. exact (eq_refl (term35 A P n x)). Qed.
Lemma lem298253 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term36 A P R n x) = (term36 A P R n x).
Proof. exact (MK_COMB (@lem298252 A P n x) (@lem298249 A P R n x)). Qed.
Lemma lem298254 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term37 A P R n) = (term37 A P R n).
Proof. exact (fun_ext (fun x : A => @lem298253 A P R n x)). Qed.
Lemma lem298255 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298256 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term38 A P R n) = (term38 A P R n).
Proof. exact (MK_COMB (@lem298255 A) (@lem298254 A P R n)). Qed.
Lemma lem298257 {A : Type'} (P : type1597 A) (R : type1594 A) : (term39 A P R) = (term39 A P R).
Proof. exact (fun_ext (fun n : nat => @lem298256 A P R n)). Qed.
Lemma lem298258 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298259 {A : Type'} (P : type1597 A) (R : type1594 A) : (term40 A P R) = (term40 A P R).
Proof. exact (MK_COMB (@lem298258) (@lem298257 A P R)). Qed.
Lemma lem298262 {A : Type'} (P : type1597 A) (a : A) : (term41 A P a) = (term41 A P a).
Proof. exact (eq_refl (term41 A P a)). Qed.
Lemma lem298263 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term42 A a P R) = (term42 A a P R).
Proof. exact (MK_COMB (@lem298262 A P a) (@lem298259 A P R)). Qed.
Lemma lem298264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem298265 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term43 A a P R) = (term43 A a P R).
Proof. exact (MK_COMB (@lem298264) (@lem298263 A a P R)). Qed.
Lemma lem298266 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term44 A a P R) = (term44 A a P R).
Proof. exact (MK_COMB (@lem298265 A a P R) (@lem298241 A a P R)). Qed.
Lemma lem298267 {A : Type'} (P : type1597 A) (R : type1594 A) : (term45 A P R) = (term45 A P R).
Proof. exact (fun_ext (fun a : A => @lem298266 A a P R)). Qed.
Lemma lem298268 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298269 {A : Type'} (P : type1597 A) (R : type1594 A) : (term46 A P R) = (term46 A P R).
Proof. exact (MK_COMB (@lem298268 A) (@lem298267 A P R)). Qed.
Lemma lem298270 {A : Type'} (P : type1597 A) : (term47 A P) = (term47 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem298269 A P R)). Qed.
Lemma lem298271 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem298272 {A : Type'} (P : type1597 A) : (term48 A P) = (term48 A P).
Proof. exact (MK_COMB (@lem298271 A) (@lem298270 A P)). Qed.
Lemma lem298273 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem298272 A P)). Qed.
Lemma lem298274 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem298275 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (MK_COMB (@lem298274 A) (@lem298273 A)). Qed.
Lemma lem298276 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298277 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem298276) (@lem298275 A)). Qed.
Lemma lem298278 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term20 A R f n) = (term20 A R f n).
Proof. exact (eq_refl (term20 A R f n)). Qed.
Lemma lem298279 {A : Type'} (R : type1594 A) (f : nat -> A) : (term21 A R f) = (term21 A R f).
Proof. exact (fun_ext (fun n : nat => @lem298278 A R f n)). Qed.
Lemma lem298280 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298281 {A : Type'} (R : type1594 A) (f : nat -> A) : (term22 A R f) = (term22 A R f).
Proof. exact (MK_COMB (@lem298280) (@lem298279 A R f)). Qed.
Lemma lem298282 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term23 A P f n) = (term23 A P f n).
Proof. exact (eq_refl (term23 A P f n)). Qed.
Lemma lem298283 {A : Type'} (P : type1597 A) (f : nat -> A) : (term24 A P f) = (term24 A P f).
Proof. exact (fun_ext (fun n : nat => @lem298282 A P f n)). Qed.
Lemma lem298284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298285 {A : Type'} (P : type1597 A) (f : nat -> A) : (term25 A P f) = (term25 A P f).
Proof. exact (MK_COMB (@lem298284) (@lem298283 A P f)). Qed.
Lemma lem298286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298287 {A : Type'} (P : type1597 A) (f : nat -> A) : (term26 A P f) = (term26 A P f).
Proof. exact (MK_COMB (@lem298286) (@lem298285 A P f)). Qed.
Lemma lem298288 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term27 A P R f) = (term27 A P R f).
Proof. exact (MK_COMB (@lem298287 A P f) (@lem298281 A R f)). Qed.
Lemma lem298289 {A : Type'} (P : type1597 A) (R : type1594 A) : (term50 A P R) = (term50 A P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem298288 A P R f)). Qed.
Lemma lem298290 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem298291 {A : Type'} (P : type1597 A) (R : type1594 A) : (term51 A P R) = (term51 A P R).
Proof. exact (MK_COMB (@lem298290 A) (@lem298289 A P R)). Qed.
Lemma lem298296 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term32 A P R n x y) = (term32 A P R n x y).
Proof. exact (eq_refl (term32 A P R n x y)). Qed.
Lemma lem298297 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term33 A P R n x) = (term33 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem298296 A P R n x y)). Qed.
Lemma lem298298 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298299 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term34 A P R n x) = (term34 A P R n x).
Proof. exact (MK_COMB (@lem298298 A) (@lem298297 A P R n x)). Qed.
Lemma lem298302 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term35 A P n x) = (term35 A P n x).
Proof. exact (eq_refl (term35 A P n x)). Qed.
Lemma lem298303 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term36 A P R n x) = (term36 A P R n x).
Proof. exact (MK_COMB (@lem298302 A P n x) (@lem298299 A P R n x)). Qed.
Lemma lem298304 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term37 A P R n) = (term37 A P R n).
Proof. exact (fun_ext (fun x : A => @lem298303 A P R n x)). Qed.
Lemma lem298305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298306 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term38 A P R n) = (term38 A P R n).
Proof. exact (MK_COMB (@lem298305 A) (@lem298304 A P R n)). Qed.
Lemma lem298307 {A : Type'} (P : type1597 A) (R : type1594 A) : (term39 A P R) = (term39 A P R).
Proof. exact (fun_ext (fun n : nat => @lem298306 A P R n)). Qed.
Lemma lem298308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298309 {A : Type'} (P : type1597 A) (R : type1594 A) : (term40 A P R) = (term40 A P R).
Proof. exact (MK_COMB (@lem298308) (@lem298307 A P R)). Qed.
Lemma lem298310 {A : Type'} (P : type1597 A) (a : A) : (term52 A P a) = (term52 A P a).
Proof. exact (eq_refl (term52 A P a)). Qed.
Lemma lem298311 {A : Type'} (P : type1597 A) : (term53 A P) = (term53 A P).
Proof. exact (fun_ext (fun a : A => @lem298310 A P a)). Qed.
Lemma lem298312 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298313 {A : Type'} (P : type1597 A) : (term54 A P) = (term54 A P).
Proof. exact (MK_COMB (@lem298312 A) (@lem298311 A P)). Qed.
Lemma lem298314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298315 {A : Type'} (P : type1597 A) : (term55 A P) = (term55 A P).
Proof. exact (MK_COMB (@lem298314) (@lem298313 A P)). Qed.
Lemma lem298316 {A : Type'} (P : type1597 A) (R : type1594 A) : (term56 A P R) = (term56 A P R).
Proof. exact (MK_COMB (@lem298315 A P) (@lem298309 A P R)). Qed.
Lemma lem298317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem298318 {A : Type'} (P : type1597 A) (R : type1594 A) : (term57 A P R) = (term57 A P R).
Proof. exact (MK_COMB (@lem298317) (@lem298316 A P R)). Qed.
Lemma lem298319 {A : Type'} (P : type1597 A) (R : type1594 A) : (term58 A P R) = (term58 A P R).
Proof. exact (MK_COMB (@lem298318 A P R) (@lem298291 A P R)). Qed.
Lemma lem298320 {A : Type'} (P : type1597 A) : (term59 A P) = (term59 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem298319 A P R)). Qed.
Lemma lem298321 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem298322 {A : Type'} (P : type1597 A) : (term60 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem298321 A) (@lem298320 A P)). Qed.
Lemma lem298323 {A : Type'} : (term61 A) = (term61 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem298322 A P)). Qed.
Lemma lem298324 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem298325 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem298324 A) (@lem298323 A)). Qed.
Lemma lem298326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298327 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem298326) (@lem298325 A)). Qed.
Lemma lem298328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem298329 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem298328) (@lem298327 A)). Qed.
Lemma lem298330 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem298329 A) (@lem298277 A)). Qed.
Lemma lem298465 {A : Type'} : (term11 A) = (term19 A).
Proof. exact (TRANS (@lem298223 A) (@lem298330 A)). Qed.
Lemma lem298466 {A : Type'} : (term19 A) = (term11 A).
Proof. exact (SYM (@lem298465 A)). Qed.
Lemma lem298467 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem298468 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem298469 {A : Type'} (P : type1597 A) (a : A) : (term52 A P a) = (term52 A P a).
Proof. exact (eq_refl (term52 A P a)). Qed.
Lemma lem298470 {A : Type'} (P : type1597 A) : (term53 A P) = (term53 A P).
Proof. exact (fun_ext (fun a : A => @lem298469 A P a)). Qed.
Lemma lem298471 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298472 {A : Type'} (P : type1597 A) : (term54 A P) = (term54 A P).
Proof. exact (MK_COMB (@lem298471 A) (@lem298470 A P)). Qed.
Lemma lem298478 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term32 A P R n x y) = (term32 A P R n x y).
Proof. exact (eq_refl (term32 A P R n x y)). Qed.
Lemma lem298479 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term33 A P R n x) = (term33 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem298478 A P R n x y)). Qed.
Lemma lem298480 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298481 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term34 A P R n x) = (term34 A P R n x).
Proof. exact (MK_COMB (@lem298480 A) (@lem298479 A P R n x)). Qed.
Lemma lem298483 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term62 A P n x) = (term62 A P n x).
Proof. exact (eq_refl (term62 A P n x)). Qed.
Lemma lem298484 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term63 A P R n x) = (term63 A P R n x).
Proof. exact (MK_COMB (@lem298483 A P n x) (@lem298481 A P R n x)). Qed.
Lemma lem298485 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term36 A P R n x) = (term63 A P R n x).
Proof. exact (@lem17265 (P n x) (term34 A P R n x)). Qed.
Lemma lem298486 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term36 A P R n x) = (term63 A P R n x).
Proof. exact (TRANS (@lem298485 A P R n x) (@lem298484 A P R n x)). Qed.
Lemma lem298487 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term37 A P R n) = (term64 A P R n).
Proof. exact (fun_ext (fun x : A => @lem298486 A P R n x)). Qed.
Lemma lem298488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298489 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term38 A P R n) = (term65 A P R n).
Proof. exact (MK_COMB (@lem298488 A) (@lem298487 A P R n)). Qed.
Lemma lem298490 {A : Type'} (P : type1597 A) (R : type1594 A) : (term39 A P R) = (term66 A P R).
Proof. exact (fun_ext (fun n : nat => @lem298489 A P R n)). Qed.
Lemma lem298491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298492 {A : Type'} (P : type1597 A) (R : type1594 A) : (term40 A P R) = (term67 A P R).
Proof. exact (MK_COMB (@lem298491) (@lem298490 A P R)). Qed.
Lemma lem298493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298494 {A : Type'} (P : type1597 A) : (term55 A P) = (term55 A P).
Proof. exact (MK_COMB (@lem298493) (@lem298472 A P)). Qed.
Lemma lem298495 {A : Type'} (P : type1597 A) (R : type1594 A) : (term56 A P R) = (term68 A P R).
Proof. exact (MK_COMB (@lem298494 A P) (@lem298492 A P R)). Qed.
Lemma lem298497 (P : nat -> Prop) : (term69 P) = (term70 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem298498 {A : Type'} (P : type1597 A) (f : nat -> A) : (term71 A P f) = (term72 A P f).
Proof. exact (@lem298497 (term24 A P f)). Qed.
Lemma lem298499 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term73 A P f n) = (term23 A P f n).
Proof. exact (eq_refl (term73 A P f n)). Qed.
Lemma lem298500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298502 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term74 A P f n) = (term75 A P f n).
Proof. exact (MK_COMB (@lem298500) (@lem298499 A P f n)). Qed.
Lemma lem298503 {A : Type'} (P : type1597 A) (f : nat -> A) : (term76 A P f) = (term77 A P f).
Proof. exact (fun_ext (fun n : nat => @lem298502 A P f n)). Qed.
Lemma lem298504 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem298505 {A : Type'} (P : type1597 A) (f : nat -> A) : (term72 A P f) = (term78 A P f).
Proof. exact (MK_COMB (@lem298504) (@lem298503 A P f)). Qed.
Lemma lem298506 {A : Type'} (P : type1597 A) (f : nat -> A) : (term71 A P f) = (term78 A P f).
Proof. exact (TRANS (@lem298498 A P f) (@lem298505 A P f)). Qed.
Lemma lem298508 (P : nat -> Prop) : (term69 P) = (term70 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem298509 {A : Type'} (R : type1594 A) (f : nat -> A) : (term79 A R f) = (term80 A R f).
Proof. exact (@lem298508 (term21 A R f)). Qed.
Lemma lem298510 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term81 A R f n) = (term20 A R f n).
Proof. exact (eq_refl (term81 A R f n)). Qed.
Lemma lem298511 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298513 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term82 A R f n) = (term83 A R f n).
Proof. exact (MK_COMB (@lem298511) (@lem298510 A R f n)). Qed.
Lemma lem298514 {A : Type'} (R : type1594 A) (f : nat -> A) : (term84 A R f) = (term85 A R f).
Proof. exact (fun_ext (fun n : nat => @lem298513 A R f n)). Qed.
Lemma lem298515 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem298516 {A : Type'} (R : type1594 A) (f : nat -> A) : (term80 A R f) = (term86 A R f).
Proof. exact (MK_COMB (@lem298515) (@lem298514 A R f)). Qed.
Lemma lem298517 {A : Type'} (R : type1594 A) (f : nat -> A) : (term79 A R f) = (term86 A R f).
Proof. exact (TRANS (@lem298509 A R f) (@lem298516 A R f)). Qed.
Lemma lem298518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem298519 {A : Type'} (P : type1597 A) (f : nat -> A) : (term87 A P f) = (term88 A P f).
Proof. exact (MK_COMB (@lem298518) (@lem298506 A P f)). Qed.
Lemma lem298520 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term89 A P R f) = (term90 A P R f).
Proof. exact (MK_COMB (@lem298519 A P f) (@lem298517 A R f)). Qed.
Lemma lem298521 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term91 A P R f) = (term89 A P R f).
Proof. exact (@lem17045 (term25 A P f) (term22 A R f)). Qed.
Lemma lem298522 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term91 A P R f) = (term90 A P R f).
Proof. exact (TRANS (@lem298521 A P R f) (@lem298520 A P R f)). Qed.
Lemma lem298523 {A : Type'} (P : type976 A) : (term92 A P) = (term93 A P).
Proof. exact (@lem18394 (nat -> A) P). Qed.
Lemma lem298524 {A : Type'} (P : type1597 A) (R : type1594 A) : (term94 A P R) = (term95 A P R).
Proof. exact (@lem298523 A (term50 A P R)). Qed.
Lemma lem298525 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term96 A P R f) = (term27 A P R f).
Proof. exact (eq_refl (term96 A P R f)). Qed.
Lemma lem298526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298527 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term97 A P R f) = (term91 A P R f).
Proof. exact (MK_COMB (@lem298526) (@lem298525 A P R f)). Qed.
Lemma lem298528 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term97 A P R f) = (term90 A P R f).
Proof. exact (TRANS (@lem298527 A P R f) (@lem298522 A P R f)). Qed.
Lemma lem298529 {A : Type'} (P : type1597 A) (R : type1594 A) : (term98 A P R) = (term99 A P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem298528 A P R f)). Qed.
Lemma lem298530 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem298531 {A : Type'} (P : type1597 A) (R : type1594 A) : (term95 A P R) = (term100 A P R).
Proof. exact (MK_COMB (@lem298530 A) (@lem298529 A P R)). Qed.
Lemma lem298532 {A : Type'} (P : type1597 A) (R : type1594 A) : (term94 A P R) = (term100 A P R).
Proof. exact (TRANS (@lem298524 A P R) (@lem298531 A P R)). Qed.
Lemma lem298533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298534 {A : Type'} (P : type1597 A) (R : type1594 A) : (term101 A P R) = (term102 A P R).
Proof. exact (MK_COMB (@lem298533) (@lem298495 A P R)). Qed.
Lemma lem298535 {A : Type'} (P : type1597 A) (R : type1594 A) : (term103 A P R) = (term104 A P R).
Proof. exact (MK_COMB (@lem298534 A P R) (@lem298532 A P R)). Qed.
Lemma lem298536 {A : Type'} (P : type1597 A) (R : type1594 A) : (term105 A P R) = (term103 A P R).
Proof. exact (@lem17362 (term56 A P R) (term51 A P R)). Qed.
Lemma lem298537 {A : Type'} (P : type1597 A) (R : type1594 A) : (term105 A P R) = (term104 A P R).
Proof. exact (TRANS (@lem298536 A P R) (@lem298535 A P R)). Qed.
Lemma lem298538 {A : Type'} (P : type937 A) : (term106 A P) = (term107 A P).
Proof. exact (@lem18392 (type1594 A) P). Qed.
Lemma lem298539 {A : Type'} (P : type1597 A) : (term108 A P) = (term109 A P).
Proof. exact (@lem298538 A (term59 A P)). Qed.
Lemma lem298540 {A : Type'} (P : type1597 A) (R : type1594 A) : (term110 A P R) = (term58 A P R).
Proof. exact (eq_refl (term110 A P R)). Qed.
Lemma lem298541 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298542 {A : Type'} (P : type1597 A) (R : type1594 A) : (term111 A P R) = (term105 A P R).
Proof. exact (MK_COMB (@lem298541) (@lem298540 A P R)). Qed.
Lemma lem298543 {A : Type'} (P : type1597 A) (R : type1594 A) : (term111 A P R) = (term104 A P R).
Proof. exact (TRANS (@lem298542 A P R) (@lem298537 A P R)). Qed.
Lemma lem298544 {A : Type'} (P : type1597 A) : (term112 A P) = (term113 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem298543 A P R)). Qed.
Lemma lem298545 {A : Type'} : (@ex (nat -> A -> A -> Prop)) = (@ex (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> A -> Prop))). Qed.
Lemma lem298546 {A : Type'} (P : type1597 A) : (term109 A P) = (term114 A P).
Proof. exact (MK_COMB (@lem298545 A) (@lem298544 A P)). Qed.
Lemma lem298547 {A : Type'} (P : type1597 A) : (term108 A P) = (term114 A P).
Proof. exact (TRANS (@lem298539 A P) (@lem298546 A P)). Qed.
Lemma lem298548 {A : Type'} (P : type953 A) : (term115 A P) = (term116 A P).
Proof. exact (@lem18392 (type1597 A) P). Qed.
Lemma lem298549 {A : Type'} : (term10 A) = (term117 A).
Proof. exact (@lem298548 A (term61 A)). Qed.
Lemma lem298550 {A : Type'} (P : type1597 A) : (term118 A P) = (term60 A P).
Proof. exact (eq_refl (term118 A P)). Qed.
Lemma lem298551 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem298552 {A : Type'} (P : type1597 A) : (term119 A P) = (term108 A P).
Proof. exact (MK_COMB (@lem298551) (@lem298550 A P)). Qed.
Lemma lem298553 {A : Type'} (P : type1597 A) : (term119 A P) = (term114 A P).
Proof. exact (TRANS (@lem298552 A P) (@lem298547 A P)). Qed.
Lemma lem298554 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem298553 A P)). Qed.
Lemma lem298555 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem298556 {A : Type'} : (term117 A) = (term122 A).
Proof. exact (MK_COMB (@lem298555 A) (@lem298554 A)). Qed.
Lemma lem298557 {A : Type'} : (term10 A) = (term122 A).
Proof. exact (TRANS (@lem298549 A) (@lem298556 A)). Qed.
Lemma lem298772 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem298773 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (@lem298772 A P Q). Qed.
Lemma lem298774 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term125 A P R n x) = (term126 A P R n x).
Proof. exact (@lem298773 A (term127 A P n x) (term33 A P R n x)). Qed.
Lemma lem298775 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term128 A P R n x y) = (term32 A P R n x y).
Proof. exact (eq_refl (term128 A P R n x y)). Qed.
Lemma lem298776 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term129 A P R n x) = (term33 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem298775 A P R n x y)). Qed.
Lemma lem298777 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298778 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term130 A P R n x) = (term34 A P R n x).
Proof. exact (MK_COMB (@lem298777 A) (@lem298776 A P R n x)). Qed.
Lemma lem298779 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term62 A P n x) = (term62 A P n x).
Proof. exact (eq_refl (term62 A P n x)). Qed.
Lemma lem298780 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term125 A P R n x) = (term63 A P R n x).
Proof. exact (MK_COMB (@lem298779 A P n x) (@lem298778 A P R n x)). Qed.
Lemma lem298781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298782 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term131 A P R n x) = (term132 A P R n x).
Proof. exact (MK_COMB (@lem298781) (@lem298780 A P R n x)). Qed.
Lemma lem298783 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term128 A P R n x y) = (term32 A P R n x y).
Proof. exact (eq_refl (term128 A P R n x y)). Qed.
Lemma lem298784 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term62 A P n x) = (term62 A P n x).
Proof. exact (eq_refl (term62 A P n x)). Qed.
Lemma lem298785 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term133 A P R n x y) = (term134 A P R n x y).
Proof. exact (MK_COMB (@lem298784 A P n x) (@lem298783 A P R n x y)). Qed.
Lemma lem298786 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term135 A P R n x) = (term136 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem298785 A P R n x y)). Qed.
Lemma lem298787 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298788 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term126 A P R n x) = (term137 A P R n x).
Proof. exact (MK_COMB (@lem298787 A) (@lem298786 A P R n x)). Qed.
Lemma lem298789 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : ((term125 A P R n x) = (term126 A P R n x)) = ((term63 A P R n x) = (term137 A P R n x)).
Proof. exact (MK_COMB (@lem298782 A P R n x) (@lem298788 A P R n x)). Qed.
Lemma lem298790 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term63 A P R n x) = (term137 A P R n x).
Proof. exact (EQ_MP (@lem298789 A P R n x) (@lem298774 A P R n x)). Qed.
Lemma lem298791 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term64 A P R n) = (term138 A P R n).
Proof. exact (fun_ext (fun x : A => @lem298790 A P R n x)). Qed.
Lemma lem298792 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298793 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term65 A P R n) = (term139 A P R n).
Proof. exact (MK_COMB (@lem298792 A) (@lem298791 A P R n)). Qed.
Lemma lem298795 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem298796 {A : Type'} (P : type1402 A) : (term142 A P) = (term143 A P).
Proof. exact (@lem298795 A A P). Qed.
Lemma lem298797 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term144 A P R n) = (term145 A P R n).
Proof. exact (@lem298796 A (term146 A P R n)). Qed.
Lemma lem298798 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term147 A P R n x) = (term136 A P R n x).
Proof. exact (eq_refl (term147 A P R n x)). Qed.
Lemma lem298799 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem298800 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term148 A P R n x y) = (term149 A P R n x y).
Proof. exact (MK_COMB (@lem298798 A P R n x) (@lem298799 A y)). Qed.
Lemma lem298801 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term149 A P R n x y) = (term134 A P R n x y).
Proof. exact (eq_refl (term149 A P R n x y)). Qed.
Lemma lem298802 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term148 A P R n x y) = (term134 A P R n x y).
Proof. exact (TRANS (@lem298800 A P R n x y) (@lem298801 A P R n x y)). Qed.
Lemma lem298803 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term150 A P R n x) = (term136 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem298802 A P R n x y)). Qed.
Lemma lem298804 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298805 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term151 A P R n x) = (term137 A P R n x).
Proof. exact (MK_COMB (@lem298804 A) (@lem298803 A P R n x)). Qed.
Lemma lem298806 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term152 A P R n) = (term138 A P R n).
Proof. exact (fun_ext (fun x : A => @lem298805 A P R n x)). Qed.
Lemma lem298807 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298808 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term144 A P R n) = (term139 A P R n).
Proof. exact (MK_COMB (@lem298807 A) (@lem298806 A P R n)). Qed.
Lemma lem298809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298810 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term153 A P R n) = (term154 A P R n).
Proof. exact (MK_COMB (@lem298809) (@lem298808 A P R n)). Qed.
Lemma lem298811 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term147 A P R n x) = (term136 A P R n x).
Proof. exact (eq_refl (term147 A P R n x)). Qed.
Lemma lem298812 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem298813 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term155 A P R n y x) = (term156 A P R n y x).
Proof. exact (MK_COMB (@lem298811 A P R n x) (@lem298812 A y x)). Qed.
Lemma lem298814 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term156 A P R n y x) = (term157 A P R n y x).
Proof. exact (eq_refl (term156 A P R n y x)). Qed.
Lemma lem298815 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) (x : A) : (term155 A P R n y x) = (term157 A P R n y x).
Proof. exact (TRANS (@lem298813 A P R n y x) (@lem298814 A P R n y x)). Qed.
Lemma lem298816 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term158 A P R n y) = (term159 A P R n y).
Proof. exact (fun_ext (fun x : A => @lem298815 A P R n y x)). Qed.
Lemma lem298817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem298818 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term160 A P R n y) = (term161 A P R n y).
Proof. exact (MK_COMB (@lem298817 A) (@lem298816 A P R n y)). Qed.
Lemma lem298819 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term162 A P R n) = (term163 A P R n).
Proof. exact (fun_ext (fun y : A -> A => @lem298818 A P R n y)). Qed.
Lemma lem298820 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem298821 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term145 A P R n) = (term164 A P R n).
Proof. exact (MK_COMB (@lem298820 A) (@lem298819 A P R n)). Qed.
Lemma lem298822 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : ((term144 A P R n) = (term145 A P R n)) = ((term139 A P R n) = (term164 A P R n)).
Proof. exact (MK_COMB (@lem298810 A P R n) (@lem298821 A P R n)). Qed.
Lemma lem298823 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term139 A P R n) = (term164 A P R n).
Proof. exact (EQ_MP (@lem298822 A P R n) (@lem298797 A P R n)). Qed.
Lemma lem298824 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term65 A P R n) = (term164 A P R n).
Proof. exact (TRANS (@lem298793 A P R n) (@lem298823 A P R n)). Qed.
Lemma lem298825 {A : Type'} (P : type1597 A) (R : type1594 A) : (term66 A P R) = (term165 A P R).
Proof. exact (fun_ext (fun n : nat => @lem298824 A P R n)). Qed.
Lemma lem298826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298827 {A : Type'} (P : type1597 A) (R : type1594 A) : (term67 A P R) = (term166 A P R).
Proof. exact (MK_COMB (@lem298826) (@lem298825 A P R)). Qed.
Lemma lem298829 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem298830 {A : Type'} (P : type1571 A) : (term167 A P) = (term168 A P).
Proof. exact (@lem298829 nat (A -> A) P). Qed.
Lemma lem298831 {A : Type'} (P : type1597 A) (R : type1594 A) : (term169 A P R) = (term170 A P R).
Proof. exact (@lem298830 A (term171 A P R)). Qed.
Lemma lem298832 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term172 A P R n) = (term163 A P R n).
Proof. exact (eq_refl (term172 A P R n)). Qed.
Lemma lem298833 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem298834 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term173 A P R n y) = (term174 A P R n y).
Proof. exact (MK_COMB (@lem298832 A P R n) (@lem298833 A y)). Qed.
Lemma lem298835 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term174 A P R n y) = (term161 A P R n y).
Proof. exact (eq_refl (term174 A P R n y)). Qed.
Lemma lem298836 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (y : A -> A) : (term173 A P R n y) = (term161 A P R n y).
Proof. exact (TRANS (@lem298834 A P R n y) (@lem298835 A P R n y)). Qed.
Lemma lem298837 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term175 A P R n) = (term163 A P R n).
Proof. exact (fun_ext (fun y : A -> A => @lem298836 A P R n y)). Qed.
Lemma lem298838 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem298839 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term176 A P R n) = (term164 A P R n).
Proof. exact (MK_COMB (@lem298838 A) (@lem298837 A P R n)). Qed.
Lemma lem298840 {A : Type'} (P : type1597 A) (R : type1594 A) : (term177 A P R) = (term165 A P R).
Proof. exact (fun_ext (fun n : nat => @lem298839 A P R n)). Qed.
Lemma lem298841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298842 {A : Type'} (P : type1597 A) (R : type1594 A) : (term169 A P R) = (term166 A P R).
Proof. exact (MK_COMB (@lem298841) (@lem298840 A P R)). Qed.
Lemma lem298843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298844 {A : Type'} (P : type1597 A) (R : type1594 A) : (term178 A P R) = (term179 A P R).
Proof. exact (MK_COMB (@lem298843) (@lem298842 A P R)). Qed.
Lemma lem298845 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term172 A P R n) = (term163 A P R n).
Proof. exact (eq_refl (term172 A P R n)). Qed.
Lemma lem298846 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (y n).
Proof. exact (eq_refl (y n)). Qed.
Lemma lem298847 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term180 A P R y n) = (term181 A P R y n).
Proof. exact (MK_COMB (@lem298845 A P R n) (@lem298846 A y n)). Qed.
Lemma lem298848 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term181 A P R y n) = (term182 A P R y n).
Proof. exact (eq_refl (term181 A P R y n)). Qed.
Lemma lem298849 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term180 A P R y n) = (term182 A P R y n).
Proof. exact (TRANS (@lem298847 A P R y n) (@lem298848 A P R y n)). Qed.
Lemma lem298850 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term183 A P R y) = (term184 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem298849 A P R y n)). Qed.
Lemma lem298851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem298852 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term185 A P R y) = (term186 A P R y).
Proof. exact (MK_COMB (@lem298851) (@lem298850 A P R y)). Qed.
Lemma lem298853 {A : Type'} (P : type1597 A) (R : type1594 A) : (term187 A P R) = (term188 A P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem298852 A P R y)). Qed.
Lemma lem298854 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem298855 {A : Type'} (P : type1597 A) (R : type1594 A) : (term170 A P R) = (term189 A P R).
Proof. exact (MK_COMB (@lem298854 A) (@lem298853 A P R)). Qed.
Lemma lem298856 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term169 A P R) = (term170 A P R)) = ((term166 A P R) = (term189 A P R)).
Proof. exact (MK_COMB (@lem298844 A P R) (@lem298855 A P R)). Qed.
Lemma lem298857 {A : Type'} (P : type1597 A) (R : type1594 A) : (term166 A P R) = (term189 A P R).
Proof. exact (EQ_MP (@lem298856 A P R) (@lem298831 A P R)). Qed.
Lemma lem298858 {A : Type'} (P : type1597 A) (R : type1594 A) : (term67 A P R) = (term189 A P R).
Proof. exact (TRANS (@lem298827 A P R) (@lem298857 A P R)). Qed.
Lemma lem298859 {A : Type'} (P : type1597 A) : (term55 A P) = (term55 A P).
Proof. exact (eq_refl (term55 A P)). Qed.
Lemma lem298860 {A : Type'} (P : type1597 A) (R : type1594 A) : (term68 A P R) = (term190 A P R).
Proof. exact (MK_COMB (@lem298859 A P) (@lem298858 A P R)). Qed.
Lemma lem298862 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem298863 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (@lem298862 A P Q). Qed.
Lemma lem298864 {A : Type'} (P : type1597 A) (R : type1594 A) : (term193 A P R) = (term194 A P R).
Proof. exact (@lem298863 A (term53 A P) (term189 A P R)). Qed.
Lemma lem298865 {A : Type'} (P : type1597 A) (a : A) : (term195 A P a) = (term52 A P a).
Proof. exact (eq_refl (term195 A P a)). Qed.
Lemma lem298866 {A : Type'} (P : type1597 A) : (term196 A P) = (term53 A P).
Proof. exact (fun_ext (fun a : A => @lem298865 A P a)). Qed.
Lemma lem298867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298868 {A : Type'} (P : type1597 A) : (term197 A P) = (term54 A P).
Proof. exact (MK_COMB (@lem298867 A) (@lem298866 A P)). Qed.
Lemma lem298869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298870 {A : Type'} (P : type1597 A) : (term198 A P) = (term55 A P).
Proof. exact (MK_COMB (@lem298869) (@lem298868 A P)). Qed.
Lemma lem298871 {A : Type'} (P : type1597 A) (R : type1594 A) : (term189 A P R) = (term189 A P R).
Proof. exact (eq_refl (term189 A P R)). Qed.
Lemma lem298872 {A : Type'} (P : type1597 A) (R : type1594 A) : (term193 A P R) = (term190 A P R).
Proof. exact (MK_COMB (@lem298870 A P) (@lem298871 A P R)). Qed.
Lemma lem298873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298874 {A : Type'} (P : type1597 A) (R : type1594 A) : (term199 A P R) = (term200 A P R).
Proof. exact (MK_COMB (@lem298873) (@lem298872 A P R)). Qed.
Lemma lem298875 {A : Type'} (P : type1597 A) (a : A) : (term195 A P a) = (term52 A P a).
Proof. exact (eq_refl (term195 A P a)). Qed.
Lemma lem298876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298877 {A : Type'} (P : type1597 A) (a : A) : (term201 A P a) = (term41 A P a).
Proof. exact (MK_COMB (@lem298876) (@lem298875 A P a)). Qed.
Lemma lem298878 {A : Type'} (P : type1597 A) (R : type1594 A) : (term189 A P R) = (term189 A P R).
Proof. exact (eq_refl (term189 A P R)). Qed.
Lemma lem298879 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term202 A a P R) = (term203 A a P R).
Proof. exact (MK_COMB (@lem298877 A P a) (@lem298878 A P R)). Qed.
Lemma lem298880 {A : Type'} (P : type1597 A) (R : type1594 A) : (term204 A P R) = (term205 A P R).
Proof. exact (fun_ext (fun a : A => @lem298879 A a P R)). Qed.
Lemma lem298881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298882 {A : Type'} (P : type1597 A) (R : type1594 A) : (term194 A P R) = (term206 A P R).
Proof. exact (MK_COMB (@lem298881 A) (@lem298880 A P R)). Qed.
Lemma lem298883 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term193 A P R) = (term194 A P R)) = ((term190 A P R) = (term206 A P R)).
Proof. exact (MK_COMB (@lem298874 A P R) (@lem298882 A P R)). Qed.
Lemma lem298884 {A : Type'} (P : type1597 A) (R : type1594 A) : (term190 A P R) = (term206 A P R).
Proof. exact (EQ_MP (@lem298883 A P R) (@lem298864 A P R)). Qed.
Lemma lem298886 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem298887 {A : Type'} (P : Prop) (Q : type938 A) : (term209 A P Q) = (term210 A P Q).
Proof. exact (@lem298886 (type1596 A) P Q). Qed.
Lemma lem298888 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term211 A a P R) = (term212 A a P R).
Proof. exact (@lem298887 A (term52 A P a) (term188 A P R)). Qed.
Lemma lem298889 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term213 A P R y) = (term186 A P R y).
Proof. exact (eq_refl (term213 A P R y)). Qed.
Lemma lem298890 {A : Type'} (P : type1597 A) (R : type1594 A) : (term214 A P R) = (term188 A P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem298889 A P R y)). Qed.
Lemma lem298891 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem298892 {A : Type'} (P : type1597 A) (R : type1594 A) : (term215 A P R) = (term189 A P R).
Proof. exact (MK_COMB (@lem298891 A) (@lem298890 A P R)). Qed.
Lemma lem298893 {A : Type'} (P : type1597 A) (a : A) : (term41 A P a) = (term41 A P a).
Proof. exact (eq_refl (term41 A P a)). Qed.
Lemma lem298894 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term211 A a P R) = (term203 A a P R).
Proof. exact (MK_COMB (@lem298893 A P a) (@lem298892 A P R)). Qed.
Lemma lem298895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298896 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term216 A a P R) = (term217 A a P R).
Proof. exact (MK_COMB (@lem298895) (@lem298894 A a P R)). Qed.
Lemma lem298897 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term213 A P R y) = (term186 A P R y).
Proof. exact (eq_refl (term213 A P R y)). Qed.
Lemma lem298898 {A : Type'} (P : type1597 A) (a : A) : (term41 A P a) = (term41 A P a).
Proof. exact (eq_refl (term41 A P a)). Qed.
Lemma lem298899 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term218 A a P R y) = (term219 A a P R y).
Proof. exact (MK_COMB (@lem298898 A P a) (@lem298897 A P R y)). Qed.
Lemma lem298900 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term220 A a P R) = (term221 A a P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem298899 A a P R y)). Qed.
Lemma lem298901 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem298902 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term212 A a P R) = (term222 A a P R).
Proof. exact (MK_COMB (@lem298901 A) (@lem298900 A a P R)). Qed.
Lemma lem298903 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : ((term211 A a P R) = (term212 A a P R)) = ((term203 A a P R) = (term222 A a P R)).
Proof. exact (MK_COMB (@lem298896 A a P R) (@lem298902 A a P R)). Qed.
Lemma lem298904 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term203 A a P R) = (term222 A a P R).
Proof. exact (EQ_MP (@lem298903 A a P R) (@lem298888 A a P R)). Qed.
Lemma lem298905 {A : Type'} (P : type1597 A) (R : type1594 A) : (term205 A P R) = (term223 A P R).
Proof. exact (fun_ext (fun a : A => @lem298904 A a P R)). Qed.
Lemma lem298906 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298907 {A : Type'} (P : type1597 A) (R : type1594 A) : (term206 A P R) = (term224 A P R).
Proof. exact (MK_COMB (@lem298906 A) (@lem298905 A P R)). Qed.
Lemma lem298908 {A : Type'} (P : type1597 A) (R : type1594 A) : (term190 A P R) = (term224 A P R).
Proof. exact (TRANS (@lem298884 A P R) (@lem298907 A P R)). Qed.
Lemma lem298909 {A : Type'} (P : type1597 A) (R : type1594 A) : (term68 A P R) = (term224 A P R).
Proof. exact (TRANS (@lem298860 A P R) (@lem298908 A P R)). Qed.
Lemma lem298910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298911 {A : Type'} (P : type1597 A) (R : type1594 A) : (term102 A P R) = (term225 A P R).
Proof. exact (MK_COMB (@lem298910) (@lem298909 A P R)). Qed.
Lemma lem298913 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term226 A P Q) = (term227 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem298914 (P : nat -> Prop) (Q : nat -> Prop) : (term228 P Q) = (term229 P Q).
Proof. exact (@lem298913 nat P Q). Qed.
Lemma lem298915 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term230 A P R f) = (term231 A P R f).
Proof. exact (@lem298914 (term77 A P f) (term85 A R f)). Qed.
Lemma lem298916 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term232 A P f n) = (term75 A P f n).
Proof. exact (eq_refl (term232 A P f n)). Qed.
Lemma lem298917 {A : Type'} (P : type1597 A) (f : nat -> A) : (term233 A P f) = (term77 A P f).
Proof. exact (fun_ext (fun n : nat => @lem298916 A P f n)). Qed.
Lemma lem298918 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem298919 {A : Type'} (P : type1597 A) (f : nat -> A) : (term234 A P f) = (term78 A P f).
Proof. exact (MK_COMB (@lem298918) (@lem298917 A P f)). Qed.
Lemma lem298920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem298921 {A : Type'} (P : type1597 A) (f : nat -> A) : (term235 A P f) = (term88 A P f).
Proof. exact (MK_COMB (@lem298920) (@lem298919 A P f)). Qed.
Lemma lem298922 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term236 A R f n) = (term83 A R f n).
Proof. exact (eq_refl (term236 A R f n)). Qed.
Lemma lem298923 {A : Type'} (R : type1594 A) (f : nat -> A) : (term237 A R f) = (term85 A R f).
Proof. exact (fun_ext (fun n : nat => @lem298922 A R f n)). Qed.
Lemma lem298924 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem298925 {A : Type'} (R : type1594 A) (f : nat -> A) : (term238 A R f) = (term86 A R f).
Proof. exact (MK_COMB (@lem298924) (@lem298923 A R f)). Qed.
Lemma lem298926 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term230 A P R f) = (term90 A P R f).
Proof. exact (MK_COMB (@lem298921 A P f) (@lem298925 A R f)). Qed.
Lemma lem298927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298928 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term239 A P R f) = (term240 A P R f).
Proof. exact (MK_COMB (@lem298927) (@lem298926 A P R f)). Qed.
Lemma lem298929 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term232 A P f n) = (term75 A P f n).
Proof. exact (eq_refl (term232 A P f n)). Qed.
Lemma lem298930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem298931 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term241 A P f n) = (term242 A P f n).
Proof. exact (MK_COMB (@lem298930) (@lem298929 A P f n)). Qed.
Lemma lem298932 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term236 A R f n) = (term83 A R f n).
Proof. exact (eq_refl (term236 A R f n)). Qed.
Lemma lem298933 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term243 A P R f n) = (term244 A P R f n).
Proof. exact (MK_COMB (@lem298931 A P f n) (@lem298932 A R f n)). Qed.
Lemma lem298934 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term245 A P R f) = (term246 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem298933 A P R f n)). Qed.
Lemma lem298935 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem298936 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term231 A P R f) = (term247 A P R f).
Proof. exact (MK_COMB (@lem298935) (@lem298934 A P R f)). Qed.
Lemma lem298937 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : ((term230 A P R f) = (term231 A P R f)) = ((term90 A P R f) = (term247 A P R f)).
Proof. exact (MK_COMB (@lem298928 A P R f) (@lem298936 A P R f)). Qed.
Lemma lem298938 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term90 A P R f) = (term247 A P R f).
Proof. exact (EQ_MP (@lem298937 A P R f) (@lem298915 A P R f)). Qed.
Lemma lem298939 {A : Type'} (P : type1597 A) (R : type1594 A) : (term99 A P R) = (term248 A P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem298938 A P R f)). Qed.
Lemma lem298940 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem298941 {A : Type'} (P : type1597 A) (R : type1594 A) : (term100 A P R) = (term249 A P R).
Proof. exact (MK_COMB (@lem298940 A) (@lem298939 A P R)). Qed.
Lemma lem298943 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem298944 {A : Type'} (P : type973 A) : (term250 A P) = (term251 A P).
Proof. exact (@lem298943 (nat -> A) nat P). Qed.
Lemma lem298945 {A : Type'} (P : type1597 A) (R : type1594 A) : (term252 A P R) = (term253 A P R).
Proof. exact (@lem298944 A (term254 A P R)). Qed.
Lemma lem298946 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term255 A P R f) = (term246 A P R f).
Proof. exact (eq_refl (term255 A P R f)). Qed.
Lemma lem298947 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem298948 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term256 A P R f n) = (term257 A P R f n).
Proof. exact (MK_COMB (@lem298946 A P R f) (@lem298947 n)). Qed.
Lemma lem298949 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term257 A P R f n) = (term244 A P R f n).
Proof. exact (eq_refl (term257 A P R f n)). Qed.
Lemma lem298950 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) (n : nat) : (term256 A P R f n) = (term244 A P R f n).
Proof. exact (TRANS (@lem298948 A P R f n) (@lem298949 A P R f n)). Qed.
Lemma lem298951 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term258 A P R f) = (term246 A P R f).
Proof. exact (fun_ext (fun n : nat => @lem298950 A P R f n)). Qed.
Lemma lem298952 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem298953 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term259 A P R f) = (term247 A P R f).
Proof. exact (MK_COMB (@lem298952) (@lem298951 A P R f)). Qed.
Lemma lem298954 {A : Type'} (P : type1597 A) (R : type1594 A) : (term260 A P R) = (term248 A P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem298953 A P R f)). Qed.
Lemma lem298955 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem298956 {A : Type'} (P : type1597 A) (R : type1594 A) : (term252 A P R) = (term249 A P R).
Proof. exact (MK_COMB (@lem298955 A) (@lem298954 A P R)). Qed.
Lemma lem298957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298958 {A : Type'} (P : type1597 A) (R : type1594 A) : (term261 A P R) = (term262 A P R).
Proof. exact (MK_COMB (@lem298957) (@lem298956 A P R)). Qed.
Lemma lem298959 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term255 A P R f) = (term246 A P R f).
Proof. exact (eq_refl (term255 A P R f)). Qed.
Lemma lem298960 {A : Type'} (n : type977 A) (f : nat -> A) : (n f) = (n f).
Proof. exact (eq_refl (n f)). Qed.
Lemma lem298961 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) (f : nat -> A) : (term263 A P R n f) = (term264 A P R n f).
Proof. exact (MK_COMB (@lem298959 A P R f) (@lem298960 A n f)). Qed.
Lemma lem298962 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) (f : nat -> A) : (term264 A P R n f) = (term265 A P R n f).
Proof. exact (eq_refl (term264 A P R n f)). Qed.
Lemma lem298963 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) (f : nat -> A) : (term263 A P R n f) = (term265 A P R n f).
Proof. exact (TRANS (@lem298961 A P R n f) (@lem298962 A P R n f)). Qed.
Lemma lem298964 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) : (term266 A P R n) = (term267 A P R n).
Proof. exact (fun_ext (fun f : nat -> A => @lem298963 A P R n f)). Qed.
Lemma lem298965 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem298966 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) : (term268 A P R n) = (term269 A P R n).
Proof. exact (MK_COMB (@lem298965 A) (@lem298964 A P R n)). Qed.
Lemma lem298967 {A : Type'} (P : type1597 A) (R : type1594 A) : (term270 A P R) = (term271 A P R).
Proof. exact (fun_ext (fun n : type977 A => @lem298966 A P R n)). Qed.
Lemma lem298968 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem298969 {A : Type'} (P : type1597 A) (R : type1594 A) : (term253 A P R) = (term272 A P R).
Proof. exact (MK_COMB (@lem298968 A) (@lem298967 A P R)). Qed.
Lemma lem298970 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term252 A P R) = (term253 A P R)) = ((term249 A P R) = (term272 A P R)).
Proof. exact (MK_COMB (@lem298958 A P R) (@lem298969 A P R)). Qed.
Lemma lem298971 {A : Type'} (P : type1597 A) (R : type1594 A) : (term249 A P R) = (term272 A P R).
Proof. exact (EQ_MP (@lem298970 A P R) (@lem298945 A P R)). Qed.
Lemma lem298972 {A : Type'} (P : type1597 A) (R : type1594 A) : (term100 A P R) = (term272 A P R).
Proof. exact (TRANS (@lem298941 A P R) (@lem298971 A P R)). Qed.
Lemma lem298973 {A : Type'} (P : type1597 A) (R : type1594 A) : (term104 A P R) = (term273 A P R).
Proof. exact (MK_COMB (@lem298911 A P R) (@lem298972 A P R)). Qed.
Lemma lem298975 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem298976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (@lem298975 A P Q). Qed.
Lemma lem298977 {A : Type'} (P : type1597 A) (R : type1594 A) : (term274 A P R) = (term275 A P R).
Proof. exact (@lem298976 A (term223 A P R) (term272 A P R)). Qed.
Lemma lem298978 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term276 A P R a) = (term222 A a P R).
Proof. exact (eq_refl (term276 A P R a)). Qed.
Lemma lem298979 {A : Type'} (P : type1597 A) (R : type1594 A) : (term277 A P R) = (term223 A P R).
Proof. exact (fun_ext (fun a : A => @lem298978 A a P R)). Qed.
Lemma lem298980 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298981 {A : Type'} (P : type1597 A) (R : type1594 A) : (term278 A P R) = (term224 A P R).
Proof. exact (MK_COMB (@lem298980 A) (@lem298979 A P R)). Qed.
Lemma lem298982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298983 {A : Type'} (P : type1597 A) (R : type1594 A) : (term279 A P R) = (term225 A P R).
Proof. exact (MK_COMB (@lem298982) (@lem298981 A P R)). Qed.
Lemma lem298984 {A : Type'} (P : type1597 A) (R : type1594 A) : (term272 A P R) = (term272 A P R).
Proof. exact (eq_refl (term272 A P R)). Qed.
Lemma lem298985 {A : Type'} (P : type1597 A) (R : type1594 A) : (term274 A P R) = (term273 A P R).
Proof. exact (MK_COMB (@lem298983 A P R) (@lem298984 A P R)). Qed.
Lemma lem298986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem298987 {A : Type'} (P : type1597 A) (R : type1594 A) : (term280 A P R) = (term281 A P R).
Proof. exact (MK_COMB (@lem298986) (@lem298985 A P R)). Qed.
Lemma lem298988 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term276 A P R a) = (term222 A a P R).
Proof. exact (eq_refl (term276 A P R a)). Qed.
Lemma lem298989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem298990 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term282 A P R a) = (term283 A a P R).
Proof. exact (MK_COMB (@lem298989) (@lem298988 A a P R)). Qed.
Lemma lem298991 {A : Type'} (P : type1597 A) (R : type1594 A) : (term272 A P R) = (term272 A P R).
Proof. exact (eq_refl (term272 A P R)). Qed.
Lemma lem298992 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term284 A a P R) = (term285 A a P R).
Proof. exact (MK_COMB (@lem298990 A a P R) (@lem298991 A P R)). Qed.
Lemma lem298993 {A : Type'} (P : type1597 A) (R : type1594 A) : (term286 A P R) = (term287 A P R).
Proof. exact (fun_ext (fun a : A => @lem298992 A a P R)). Qed.
Lemma lem298994 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem298995 {A : Type'} (P : type1597 A) (R : type1594 A) : (term275 A P R) = (term288 A P R).
Proof. exact (MK_COMB (@lem298994 A) (@lem298993 A P R)). Qed.
Lemma lem298996 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term274 A P R) = (term275 A P R)) = ((term273 A P R) = (term288 A P R)).
Proof. exact (MK_COMB (@lem298987 A P R) (@lem298995 A P R)). Qed.
Lemma lem298997 {A : Type'} (P : type1597 A) (R : type1594 A) : (term273 A P R) = (term288 A P R).
Proof. exact (EQ_MP (@lem298996 A P R) (@lem298977 A P R)). Qed.
Lemma lem298999 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem299000 {A : Type'} (P : type938 A) (Q : Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (@lem298999 (type1596 A) P Q). Qed.
Lemma lem299001 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term291 A a P R) = (term292 A a P R).
Proof. exact (@lem299000 A (term221 A a P R) (term272 A P R)). Qed.
Lemma lem299002 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term293 A a P R y) = (term219 A a P R y).
Proof. exact (eq_refl (term293 A a P R y)). Qed.
Lemma lem299003 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term294 A a P R) = (term221 A a P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem299002 A a P R y)). Qed.
Lemma lem299004 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem299005 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term295 A a P R) = (term222 A a P R).
Proof. exact (MK_COMB (@lem299004 A) (@lem299003 A a P R)). Qed.
Lemma lem299006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem299007 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term296 A a P R) = (term283 A a P R).
Proof. exact (MK_COMB (@lem299006) (@lem299005 A a P R)). Qed.
Lemma lem299008 {A : Type'} (P : type1597 A) (R : type1594 A) : (term272 A P R) = (term272 A P R).
Proof. exact (eq_refl (term272 A P R)). Qed.
Lemma lem299009 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term291 A a P R) = (term285 A a P R).
Proof. exact (MK_COMB (@lem299007 A a P R) (@lem299008 A P R)). Qed.
Lemma lem299010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299011 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term297 A a P R) = (term298 A a P R).
Proof. exact (MK_COMB (@lem299010) (@lem299009 A a P R)). Qed.
Lemma lem299012 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term293 A a P R y) = (term219 A a P R y).
Proof. exact (eq_refl (term293 A a P R y)). Qed.
Lemma lem299013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem299014 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term299 A a P R y) = (term300 A a P R y).
Proof. exact (MK_COMB (@lem299013) (@lem299012 A a P R y)). Qed.
Lemma lem299015 {A : Type'} (P : type1597 A) (R : type1594 A) : (term272 A P R) = (term272 A P R).
Proof. exact (eq_refl (term272 A P R)). Qed.
Lemma lem299016 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term301 A a y P R) = (term302 A a y P R).
Proof. exact (MK_COMB (@lem299014 A a P R y) (@lem299015 A P R)). Qed.
Lemma lem299017 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term303 A a P R) = (term304 A a P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem299016 A a y P R)). Qed.
Lemma lem299018 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem299019 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term292 A a P R) = (term305 A a P R).
Proof. exact (MK_COMB (@lem299018 A) (@lem299017 A a P R)). Qed.
Lemma lem299020 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : ((term291 A a P R) = (term292 A a P R)) = ((term285 A a P R) = (term305 A a P R)).
Proof. exact (MK_COMB (@lem299011 A a P R) (@lem299019 A a P R)). Qed.
Lemma lem299021 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term285 A a P R) = (term305 A a P R).
Proof. exact (EQ_MP (@lem299020 A a P R) (@lem299001 A a P R)). Qed.
Lemma lem299023 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem299024 {A : Type'} (P : Prop) (Q : type246 A) : (term306 A P Q) = (term307 A P Q).
Proof. exact (@lem299023 (type977 A) P Q). Qed.
Lemma lem299025 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term308 A a y P R) = (term309 A a y P R).
Proof. exact (@lem299024 A (term219 A a P R y) (term271 A P R)). Qed.
Lemma lem299026 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) : (term310 A P R n) = (term269 A P R n).
Proof. exact (eq_refl (term310 A P R n)). Qed.
Lemma lem299027 {A : Type'} (P : type1597 A) (R : type1594 A) : (term311 A P R) = (term271 A P R).
Proof. exact (fun_ext (fun n : type977 A => @lem299026 A P R n)). Qed.
Lemma lem299028 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem299029 {A : Type'} (P : type1597 A) (R : type1594 A) : (term312 A P R) = (term272 A P R).
Proof. exact (MK_COMB (@lem299028 A) (@lem299027 A P R)). Qed.
Lemma lem299030 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term300 A a P R y) = (term300 A a P R y).
Proof. exact (eq_refl (term300 A a P R y)). Qed.
Lemma lem299031 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term308 A a y P R) = (term302 A a y P R).
Proof. exact (MK_COMB (@lem299030 A a P R y) (@lem299029 A P R)). Qed.
Lemma lem299032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299033 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term313 A a y P R) = (term314 A a y P R).
Proof. exact (MK_COMB (@lem299032) (@lem299031 A a y P R)). Qed.
Lemma lem299034 {A : Type'} (P : type1597 A) (R : type1594 A) (n : type977 A) : (term310 A P R n) = (term269 A P R n).
Proof. exact (eq_refl (term310 A P R n)). Qed.
Lemma lem299035 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term300 A a P R y) = (term300 A a P R y).
Proof. exact (eq_refl (term300 A a P R y)). Qed.
Lemma lem299036 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n : type977 A) : (term315 A a y P R n) = (term316 A a y P R n).
Proof. exact (MK_COMB (@lem299035 A a P R y) (@lem299034 A P R n)). Qed.
Lemma lem299037 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term317 A a y P R) = (term318 A a y P R).
Proof. exact (fun_ext (fun n : type977 A => @lem299036 A a y P R n)). Qed.
Lemma lem299038 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem299039 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term309 A a y P R) = (term319 A a y P R).
Proof. exact (MK_COMB (@lem299038 A) (@lem299037 A a y P R)). Qed.
Lemma lem299040 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : ((term308 A a y P R) = (term309 A a y P R)) = ((term302 A a y P R) = (term319 A a y P R)).
Proof. exact (MK_COMB (@lem299033 A a y P R) (@lem299039 A a y P R)). Qed.
Lemma lem299041 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) : (term302 A a y P R) = (term319 A a y P R).
Proof. exact (EQ_MP (@lem299040 A a y P R) (@lem299025 A a y P R)). Qed.
Lemma lem299042 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term304 A a P R) = (term320 A a P R).
Proof. exact (fun_ext (fun y : type1596 A => @lem299041 A a y P R)). Qed.
Lemma lem299043 {A : Type'} : (@ex (nat -> A -> A)) = (@ex (nat -> A -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> A))). Qed.
Lemma lem299044 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term305 A a P R) = (term321 A a P R).
Proof. exact (MK_COMB (@lem299043 A) (@lem299042 A a P R)). Qed.
Lemma lem299045 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term285 A a P R) = (term321 A a P R).
Proof. exact (TRANS (@lem299021 A a P R) (@lem299044 A a P R)). Qed.
Lemma lem299046 {A : Type'} (P : type1597 A) (R : type1594 A) : (term287 A P R) = (term322 A P R).
Proof. exact (fun_ext (fun a : A => @lem299045 A a P R)). Qed.
Lemma lem299047 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299048 {A : Type'} (P : type1597 A) (R : type1594 A) : (term288 A P R) = (term323 A P R).
Proof. exact (MK_COMB (@lem299047 A) (@lem299046 A P R)). Qed.
Lemma lem299049 {A : Type'} (P : type1597 A) (R : type1594 A) : (term273 A P R) = (term323 A P R).
Proof. exact (TRANS (@lem298997 A P R) (@lem299048 A P R)). Qed.
Lemma lem299050 {A : Type'} (P : type1597 A) (R : type1594 A) : (term104 A P R) = (term323 A P R).
Proof. exact (TRANS (@lem298973 A P R) (@lem299049 A P R)). Qed.
Lemma lem299051 {A : Type'} (P : type1597 A) : (term113 A P) = (term324 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299050 A P R)). Qed.
Lemma lem299052 {A : Type'} : (@ex (nat -> A -> A -> Prop)) = (@ex (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> A -> Prop))). Qed.
Lemma lem299053 {A : Type'} (P : type1597 A) : (term114 A P) = (term325 A P).
Proof. exact (MK_COMB (@lem299052 A) (@lem299051 A P)). Qed.
Lemma lem299054 {A : Type'} : (term121 A) = (term326 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem299053 A P)). Qed.
Lemma lem299055 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem299057 {A : Type'} : (term122 A) = (term327 A).
Proof. exact (MK_COMB (@lem299055 A) (@lem299054 A)). Qed.
Lemma lem299058 {A : Type'} : (term10 A) = (term327 A).
Proof. exact (TRANS (@lem298557 A) (@lem299057 A)). Qed.
Lemma lem299059 {A : Type'} (h1 : term10 A) : term327 A.
Proof. exact (EQ_MP (@lem299058 A) (@lem298467 A h1)). Qed.
Lemma lem299068 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term328 A P R n x y) = (term329 A P R n x y).
Proof. exact (@lem17045 (term330 A P n y) (R n x y)). Qed.
Lemma lem299069 {A : Type'} (P : A -> Prop) : (term331 A P) = (term332 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem299070 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term333 A P R n x) = (term334 A P R n x).
Proof. exact (@lem299069 A (term33 A P R n x)). Qed.
Lemma lem299071 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term128 A P R n x y) = (term32 A P R n x y).
Proof. exact (eq_refl (term128 A P R n x y)). Qed.
Lemma lem299072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem299073 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term335 A P R n x y) = (term328 A P R n x y).
Proof. exact (MK_COMB (@lem299072) (@lem299071 A P R n x y)). Qed.
Lemma lem299074 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) (y : A) : (term335 A P R n x y) = (term329 A P R n x y).
Proof. exact (TRANS (@lem299073 A P R n x y) (@lem299068 A P R n x y)). Qed.
Lemma lem299075 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term336 A P R n x) = (term337 A P R n x).
Proof. exact (fun_ext (fun y : A => @lem299074 A P R n x y)). Qed.
Lemma lem299076 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299077 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term334 A P R n x) = (term338 A P R n x).
Proof. exact (MK_COMB (@lem299076 A) (@lem299075 A P R n x)). Qed.
Lemma lem299078 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term333 A P R n x) = (term338 A P R n x).
Proof. exact (TRANS (@lem299070 A P R n x) (@lem299077 A P R n x)). Qed.
Lemma lem299080 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term339 A P n x) = (term339 A P n x).
Proof. exact (eq_refl (term339 A P n x)). Qed.
Lemma lem299081 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term340 A P R n x) = (term341 A P R n x).
Proof. exact (MK_COMB (@lem299080 A P n x) (@lem299078 A P R n x)). Qed.
Lemma lem299082 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term342 A P R n x) = (term340 A P R n x).
Proof. exact (@lem17362 (P n x) (term34 A P R n x)). Qed.
Lemma lem299083 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term342 A P R n x) = (term341 A P R n x).
Proof. exact (TRANS (@lem299082 A P R n x) (@lem299081 A P R n x)). Qed.
Lemma lem299084 {A : Type'} (P : A -> Prop) : (term343 A P) = (term344 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem299085 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term345 A P R n) = (term346 A P R n).
Proof. exact (@lem299084 A (term37 A P R n)). Qed.
Lemma lem299086 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term347 A P R n x) = (term36 A P R n x).
Proof. exact (eq_refl (term347 A P R n x)). Qed.
Lemma lem299087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem299088 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term348 A P R n x) = (term342 A P R n x).
Proof. exact (MK_COMB (@lem299087) (@lem299086 A P R n x)). Qed.
Lemma lem299089 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term348 A P R n x) = (term341 A P R n x).
Proof. exact (TRANS (@lem299088 A P R n x) (@lem299083 A P R n x)). Qed.
Lemma lem299090 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term349 A P R n) = (term350 A P R n).
Proof. exact (fun_ext (fun x : A => @lem299089 A P R n x)). Qed.
Lemma lem299091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299092 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term346 A P R n) = (term351 A P R n).
Proof. exact (MK_COMB (@lem299091 A) (@lem299090 A P R n)). Qed.
Lemma lem299093 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term345 A P R n) = (term351 A P R n).
Proof. exact (TRANS (@lem299085 A P R n) (@lem299092 A P R n)). Qed.
Lemma lem299094 (P : nat -> Prop) : (term69 P) = (term70 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem299095 {A : Type'} (P : type1597 A) (R : type1594 A) : (term352 A P R) = (term353 A P R).
Proof. exact (@lem299094 (term39 A P R)). Qed.
Lemma lem299096 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term354 A P R n) = (term38 A P R n).
Proof. exact (eq_refl (term354 A P R n)). Qed.
Lemma lem299097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem299098 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term355 A P R n) = (term345 A P R n).
Proof. exact (MK_COMB (@lem299097) (@lem299096 A P R n)). Qed.
Lemma lem299099 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term355 A P R n) = (term351 A P R n).
Proof. exact (TRANS (@lem299098 A P R n) (@lem299093 A P R n)). Qed.
Lemma lem299100 {A : Type'} (P : type1597 A) (R : type1594 A) : (term356 A P R) = (term357 A P R).
Proof. exact (fun_ext (fun n : nat => @lem299099 A P R n)). Qed.
Lemma lem299101 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299102 {A : Type'} (P : type1597 A) (R : type1594 A) : (term353 A P R) = (term358 A P R).
Proof. exact (MK_COMB (@lem299101) (@lem299100 A P R)). Qed.
Lemma lem299103 {A : Type'} (P : type1597 A) (R : type1594 A) : (term352 A P R) = (term358 A P R).
Proof. exact (TRANS (@lem299095 A P R) (@lem299102 A P R)). Qed.
Lemma lem299105 {A : Type'} (P : type1597 A) (a : A) : (term359 A P a) = (term359 A P a).
Proof. exact (eq_refl (term359 A P a)). Qed.
Lemma lem299106 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term360 A a P R) = (term361 A a P R).
Proof. exact (MK_COMB (@lem299105 A P a) (@lem299103 A P R)). Qed.
Lemma lem299107 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term362 A a P R) = (term360 A a P R).
Proof. exact (@lem17045 (term52 A P a) (term40 A P R)). Qed.
Lemma lem299108 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term362 A a P R) = (term361 A a P R).
Proof. exact (TRANS (@lem299107 A a P R) (@lem299106 A a P R)). Qed.
Lemma lem299110 {A : Type'} (P : type1597 A) (f : nat -> A) (n : nat) : (term23 A P f n) = (term23 A P f n).
Proof. exact (eq_refl (term23 A P f n)). Qed.
Lemma lem299111 {A : Type'} (P : type1597 A) (f : nat -> A) : (term24 A P f) = (term24 A P f).
Proof. exact (fun_ext (fun n : nat => @lem299110 A P f n)). Qed.
Lemma lem299112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem299113 {A : Type'} (P : type1597 A) (f : nat -> A) : (term25 A P f) = (term25 A P f).
Proof. exact (MK_COMB (@lem299112) (@lem299111 A P f)). Qed.
Lemma lem299114 {A : Type'} (R : type1594 A) (f : nat -> A) (n : nat) : (term20 A R f n) = (term20 A R f n).
Proof. exact (eq_refl (term20 A R f n)). Qed.
Lemma lem299115 {A : Type'} (R : type1594 A) (f : nat -> A) : (term21 A R f) = (term21 A R f).
Proof. exact (fun_ext (fun n : nat => @lem299114 A R f n)). Qed.
Lemma lem299116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem299117 {A : Type'} (R : type1594 A) (f : nat -> A) : (term22 A R f) = (term22 A R f).
Proof. exact (MK_COMB (@lem299116) (@lem299115 A R f)). Qed.
Lemma lem299118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem299119 {A : Type'} (P : type1597 A) (f : nat -> A) : (term26 A P f) = (term26 A P f).
Proof. exact (MK_COMB (@lem299118) (@lem299113 A P f)). Qed.
Lemma lem299120 {A : Type'} (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term27 A P R f) = (term27 A P R f).
Proof. exact (MK_COMB (@lem299119 A P f) (@lem299117 A R f)). Qed.
Lemma lem299122 {A : Type'} (f : nat -> A) (a : A) : (term28 A f a) = (term28 A f a).
Proof. exact (eq_refl (term28 A f a)). Qed.
Lemma lem299123 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term29 A a P R f) = (term29 A a P R f).
Proof. exact (MK_COMB (@lem299122 A f a) (@lem299120 A P R f)). Qed.
Lemma lem299124 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term30 A a P R) = (term30 A a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem299123 A a P R f)). Qed.
Lemma lem299125 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem299126 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (MK_COMB (@lem299125 A) (@lem299124 A a P R)). Qed.
Lemma lem299127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem299128 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term363 A a P R) = (term364 A a P R).
Proof. exact (MK_COMB (@lem299127) (@lem299108 A a P R)). Qed.
Lemma lem299129 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term365 A a P R) = (term366 A a P R).
Proof. exact (MK_COMB (@lem299128 A a P R) (@lem299126 A a P R)). Qed.
Lemma lem299130 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term44 A a P R) = (term365 A a P R).
Proof. exact (@lem17265 (term42 A a P R) (term31 A a P R)). Qed.
Lemma lem299131 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term44 A a P R) = (term366 A a P R).
Proof. exact (TRANS (@lem299130 A a P R) (@lem299129 A a P R)). Qed.
Lemma lem299132 {A : Type'} (P : type1597 A) (R : type1594 A) : (term45 A P R) = (term367 A P R).
Proof. exact (fun_ext (fun a : A => @lem299131 A a P R)). Qed.
Lemma lem299133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299134 {A : Type'} (P : type1597 A) (R : type1594 A) : (term46 A P R) = (term368 A P R).
Proof. exact (MK_COMB (@lem299133 A) (@lem299132 A P R)). Qed.
Lemma lem299135 {A : Type'} (P : type1597 A) : (term47 A P) = (term369 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299134 A P R)). Qed.
Lemma lem299136 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299137 {A : Type'} (P : type1597 A) : (term48 A P) = (term370 A P).
Proof. exact (MK_COMB (@lem299136 A) (@lem299135 A P)). Qed.
Lemma lem299138 {A : Type'} : (term49 A) = (term371 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem299137 A P)). Qed.
Lemma lem299139 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299140 {A : Type'} : (term17 A) = (term372 A).
Proof. exact (MK_COMB (@lem299139 A) (@lem299138 A)). Qed.
Lemma lem299355 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem299356 (P : Prop) (Q : nat -> Prop) : (term373 P Q) = (term374 P Q).
Proof. exact (@lem299355 nat P Q). Qed.
Lemma lem299357 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term375 A a P R) = (term376 A a P R).
Proof. exact (@lem299356 (term377 A P a) (term357 A P R)). Qed.
Lemma lem299358 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term378 A P R n) = (term351 A P R n).
Proof. exact (eq_refl (term378 A P R n)). Qed.
Lemma lem299359 {A : Type'} (P : type1597 A) (R : type1594 A) : (term379 A P R) = (term357 A P R).
Proof. exact (fun_ext (fun n : nat => @lem299358 A P R n)). Qed.
Lemma lem299360 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299361 {A : Type'} (P : type1597 A) (R : type1594 A) : (term380 A P R) = (term358 A P R).
Proof. exact (MK_COMB (@lem299360) (@lem299359 A P R)). Qed.
Lemma lem299362 {A : Type'} (P : type1597 A) (a : A) : (term359 A P a) = (term359 A P a).
Proof. exact (eq_refl (term359 A P a)). Qed.
Lemma lem299363 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term375 A a P R) = (term361 A a P R).
Proof. exact (MK_COMB (@lem299362 A P a) (@lem299361 A P R)). Qed.
Lemma lem299364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299365 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term381 A a P R) = (term382 A a P R).
Proof. exact (MK_COMB (@lem299364) (@lem299363 A a P R)). Qed.
Lemma lem299366 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term378 A P R n) = (term351 A P R n).
Proof. exact (eq_refl (term378 A P R n)). Qed.
Lemma lem299367 {A : Type'} (P : type1597 A) (a : A) : (term359 A P a) = (term359 A P a).
Proof. exact (eq_refl (term359 A P a)). Qed.
Lemma lem299368 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term383 A a P R n) = (term384 A a P R n).
Proof. exact (MK_COMB (@lem299367 A P a) (@lem299366 A P R n)). Qed.
Lemma lem299369 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term385 A a P R) = (term386 A a P R).
Proof. exact (fun_ext (fun n : nat => @lem299368 A a P R n)). Qed.
Lemma lem299370 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299371 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term376 A a P R) = (term387 A a P R).
Proof. exact (MK_COMB (@lem299370) (@lem299369 A a P R)). Qed.
Lemma lem299372 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : ((term375 A a P R) = (term376 A a P R)) = ((term361 A a P R) = (term387 A a P R)).
Proof. exact (MK_COMB (@lem299365 A a P R) (@lem299371 A a P R)). Qed.
Lemma lem299373 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term361 A a P R) = (term387 A a P R).
Proof. exact (EQ_MP (@lem299372 A a P R) (@lem299357 A a P R)). Qed.
Lemma lem299375 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem299376 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (@lem299375 A P Q). Qed.
Lemma lem299377 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term388 A a P R n) = (term389 A a P R n).
Proof. exact (@lem299376 A (term377 A P a) (term350 A P R n)). Qed.
Lemma lem299378 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term390 A P R n x) = (term341 A P R n x).
Proof. exact (eq_refl (term390 A P R n x)). Qed.
Lemma lem299379 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term391 A P R n) = (term350 A P R n).
Proof. exact (fun_ext (fun x : A => @lem299378 A P R n x)). Qed.
Lemma lem299380 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299381 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) : (term392 A P R n) = (term351 A P R n).
Proof. exact (MK_COMB (@lem299380 A) (@lem299379 A P R n)). Qed.
Lemma lem299382 {A : Type'} (P : type1597 A) (a : A) : (term359 A P a) = (term359 A P a).
Proof. exact (eq_refl (term359 A P a)). Qed.
Lemma lem299383 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term388 A a P R n) = (term384 A a P R n).
Proof. exact (MK_COMB (@lem299382 A P a) (@lem299381 A P R n)). Qed.
Lemma lem299384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299385 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term393 A a P R n) = (term394 A a P R n).
Proof. exact (MK_COMB (@lem299384) (@lem299383 A a P R n)). Qed.
Lemma lem299386 {A : Type'} (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term390 A P R n x) = (term341 A P R n x).
Proof. exact (eq_refl (term390 A P R n x)). Qed.
Lemma lem299387 {A : Type'} (P : type1597 A) (a : A) : (term359 A P a) = (term359 A P a).
Proof. exact (eq_refl (term359 A P a)). Qed.
Lemma lem299388 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term395 A a P R n x) = (term396 A a P R n x).
Proof. exact (MK_COMB (@lem299387 A P a) (@lem299386 A P R n x)). Qed.
Lemma lem299389 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term397 A a P R n) = (term398 A a P R n).
Proof. exact (fun_ext (fun x : A => @lem299388 A a P R n x)). Qed.
Lemma lem299390 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299391 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term389 A a P R n) = (term399 A a P R n).
Proof. exact (MK_COMB (@lem299390 A) (@lem299389 A a P R n)). Qed.
Lemma lem299392 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : ((term388 A a P R n) = (term389 A a P R n)) = ((term384 A a P R n) = (term399 A a P R n)).
Proof. exact (MK_COMB (@lem299385 A a P R n) (@lem299391 A a P R n)). Qed.
Lemma lem299393 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term384 A a P R n) = (term399 A a P R n).
Proof. exact (EQ_MP (@lem299392 A a P R n) (@lem299377 A a P R n)). Qed.
Lemma lem299394 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term386 A a P R) = (term400 A a P R).
Proof. exact (fun_ext (fun n : nat => @lem299393 A a P R n)). Qed.
Lemma lem299395 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299396 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term387 A a P R) = (term401 A a P R).
Proof. exact (MK_COMB (@lem299395) (@lem299394 A a P R)). Qed.
Lemma lem299397 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term361 A a P R) = (term401 A a P R).
Proof. exact (TRANS (@lem299373 A a P R) (@lem299396 A a P R)). Qed.
Lemma lem299398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem299399 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term364 A a P R) = (term402 A a P R).
Proof. exact (MK_COMB (@lem299398) (@lem299397 A a P R)). Qed.
Lemma lem299400 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (eq_refl (term31 A a P R)). Qed.
Lemma lem299401 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term366 A a P R) = (term403 A a P R).
Proof. exact (MK_COMB (@lem299399 A a P R) (@lem299400 A a P R)). Qed.
Lemma lem299405 {A : Type'} (P : A -> Prop) (Q : Prop) : (term404 A P Q) = (term405 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem299406 (P : nat -> Prop) (Q : Prop) : (term406 P Q) = (term407 P Q).
Proof. exact (@lem299405 nat P Q). Qed.
Lemma lem299407 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term408 A a P R) = (term409 A a P R).
Proof. exact (@lem299406 (term400 A a P R) (term31 A a P R)). Qed.
Lemma lem299408 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term410 A a P R n) = (term399 A a P R n).
Proof. exact (eq_refl (term410 A a P R n)). Qed.
Lemma lem299409 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term411 A a P R) = (term400 A a P R).
Proof. exact (fun_ext (fun n : nat => @lem299408 A a P R n)). Qed.
Lemma lem299410 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299411 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term412 A a P R) = (term401 A a P R).
Proof. exact (MK_COMB (@lem299410) (@lem299409 A a P R)). Qed.
Lemma lem299412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem299413 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term413 A a P R) = (term402 A a P R).
Proof. exact (MK_COMB (@lem299412) (@lem299411 A a P R)). Qed.
Lemma lem299414 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (eq_refl (term31 A a P R)). Qed.
Lemma lem299415 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term408 A a P R) = (term403 A a P R).
Proof. exact (MK_COMB (@lem299413 A a P R) (@lem299414 A a P R)). Qed.
Lemma lem299416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299417 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term414 A a P R) = (term415 A a P R).
Proof. exact (MK_COMB (@lem299416) (@lem299415 A a P R)). Qed.
Lemma lem299418 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term410 A a P R n) = (term399 A a P R n).
Proof. exact (eq_refl (term410 A a P R n)). Qed.
Lemma lem299419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem299420 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term416 A a P R n) = (term417 A a P R n).
Proof. exact (MK_COMB (@lem299419) (@lem299418 A a P R n)). Qed.
Lemma lem299421 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (eq_refl (term31 A a P R)). Qed.
Lemma lem299422 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term418 A n a P R) = (term419 A n a P R).
Proof. exact (MK_COMB (@lem299420 A a P R n) (@lem299421 A a P R)). Qed.
Lemma lem299423 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term420 A a P R) = (term421 A a P R).
Proof. exact (fun_ext (fun n : nat => @lem299422 A n a P R)). Qed.
Lemma lem299424 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299425 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term409 A a P R) = (term422 A a P R).
Proof. exact (MK_COMB (@lem299424) (@lem299423 A a P R)). Qed.
Lemma lem299426 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : ((term408 A a P R) = (term409 A a P R)) = ((term403 A a P R) = (term422 A a P R)).
Proof. exact (MK_COMB (@lem299417 A a P R) (@lem299425 A a P R)). Qed.
Lemma lem299427 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term403 A a P R) = (term422 A a P R).
Proof. exact (EQ_MP (@lem299426 A a P R) (@lem299407 A a P R)). Qed.
Lemma lem299431 {A : Type'} (P : A -> Prop) (Q : Prop) : (term404 A P Q) = (term405 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem299432 {A : Type'} (P : A -> Prop) (Q : Prop) : (term404 A P Q) = (term405 A P Q).
Proof. exact (@lem299431 A P Q). Qed.
Lemma lem299433 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term423 A n a P R) = (term424 A n a P R).
Proof. exact (@lem299432 A (term398 A a P R n) (term31 A a P R)). Qed.
Lemma lem299434 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term425 A a P R n x) = (term396 A a P R n x).
Proof. exact (eq_refl (term425 A a P R n x)). Qed.
Lemma lem299435 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term426 A a P R n) = (term398 A a P R n).
Proof. exact (fun_ext (fun x : A => @lem299434 A a P R n x)). Qed.
Lemma lem299436 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299437 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term427 A a P R n) = (term399 A a P R n).
Proof. exact (MK_COMB (@lem299436 A) (@lem299435 A a P R n)). Qed.
Lemma lem299438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem299439 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term428 A a P R n) = (term417 A a P R n).
Proof. exact (MK_COMB (@lem299438) (@lem299437 A a P R n)). Qed.
Lemma lem299440 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (eq_refl (term31 A a P R)). Qed.
Lemma lem299441 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term423 A n a P R) = (term419 A n a P R).
Proof. exact (MK_COMB (@lem299439 A a P R n) (@lem299440 A a P R)). Qed.
Lemma lem299442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299443 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term429 A n a P R) = (term430 A n a P R).
Proof. exact (MK_COMB (@lem299442) (@lem299441 A n a P R)). Qed.
Lemma lem299444 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term425 A a P R n x) = (term396 A a P R n x).
Proof. exact (eq_refl (term425 A a P R n x)). Qed.
Lemma lem299445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem299446 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term431 A a P R n x) = (term432 A a P R n x).
Proof. exact (MK_COMB (@lem299445) (@lem299444 A a P R n x)). Qed.
Lemma lem299447 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term31 A a P R) = (term31 A a P R).
Proof. exact (eq_refl (term31 A a P R)). Qed.
Lemma lem299448 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term433 A n x a P R) = (term434 A n x a P R).
Proof. exact (MK_COMB (@lem299446 A a P R n x) (@lem299447 A a P R)). Qed.
Lemma lem299449 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term435 A n a P R) = (term436 A n a P R).
Proof. exact (fun_ext (fun x : A => @lem299448 A n x a P R)). Qed.
Lemma lem299450 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299451 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term424 A n a P R) = (term437 A n a P R).
Proof. exact (MK_COMB (@lem299450 A) (@lem299449 A n a P R)). Qed.
Lemma lem299452 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : ((term423 A n a P R) = (term424 A n a P R)) = ((term419 A n a P R) = (term437 A n a P R)).
Proof. exact (MK_COMB (@lem299443 A n a P R) (@lem299451 A n a P R)). Qed.
Lemma lem299453 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term419 A n a P R) = (term437 A n a P R).
Proof. exact (EQ_MP (@lem299452 A n a P R) (@lem299433 A n a P R)). Qed.
Lemma lem299455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem299456 {A : Type'} (P : Prop) (Q : type976 A) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem299455 (nat -> A) P Q). Qed.
Lemma lem299457 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term440 A n x a P R) = (term441 A n x a P R).
Proof. exact (@lem299456 A (term396 A a P R n x) (term30 A a P R)). Qed.
Lemma lem299458 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term442 A a P R f) = (term29 A a P R f).
Proof. exact (eq_refl (term442 A a P R f)). Qed.
Lemma lem299459 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term443 A a P R) = (term30 A a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem299458 A a P R f)). Qed.
Lemma lem299460 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem299461 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term444 A a P R) = (term31 A a P R).
Proof. exact (MK_COMB (@lem299460 A) (@lem299459 A a P R)). Qed.
Lemma lem299462 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term432 A a P R n x) = (term432 A a P R n x).
Proof. exact (eq_refl (term432 A a P R n x)). Qed.
Lemma lem299463 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term440 A n x a P R) = (term434 A n x a P R).
Proof. exact (MK_COMB (@lem299462 A a P R n x) (@lem299461 A a P R)). Qed.
Lemma lem299464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299465 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term445 A n x a P R) = (term446 A n x a P R).
Proof. exact (MK_COMB (@lem299464) (@lem299463 A n x a P R)). Qed.
Lemma lem299466 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term442 A a P R f) = (term29 A a P R f).
Proof. exact (eq_refl (term442 A a P R f)). Qed.
Lemma lem299467 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) (x : A) : (term432 A a P R n x) = (term432 A a P R n x).
Proof. exact (eq_refl (term432 A a P R n x)). Qed.
Lemma lem299468 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term447 A n x a P R f) = (term448 A n x a P R f).
Proof. exact (MK_COMB (@lem299467 A a P R n x) (@lem299466 A a P R f)). Qed.
Lemma lem299469 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term449 A n x a P R) = (term450 A n x a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem299468 A n x a P R f)). Qed.
Lemma lem299470 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem299471 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term441 A n x a P R) = (term451 A n x a P R).
Proof. exact (MK_COMB (@lem299470 A) (@lem299469 A n x a P R)). Qed.
Lemma lem299472 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : ((term440 A n x a P R) = (term441 A n x a P R)) = ((term434 A n x a P R) = (term451 A n x a P R)).
Proof. exact (MK_COMB (@lem299465 A n x a P R) (@lem299471 A n x a P R)). Qed.
Lemma lem299473 {A : Type'} (n : nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term434 A n x a P R) = (term451 A n x a P R).
Proof. exact (EQ_MP (@lem299472 A n x a P R) (@lem299457 A n x a P R)). Qed.
Lemma lem299474 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term436 A n a P R) = (term452 A n a P R).
Proof. exact (fun_ext (fun x : A => @lem299473 A n x a P R)). Qed.
Lemma lem299475 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299476 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term437 A n a P R) = (term453 A n a P R).
Proof. exact (MK_COMB (@lem299475 A) (@lem299474 A n a P R)). Qed.
Lemma lem299477 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term419 A n a P R) = (term453 A n a P R).
Proof. exact (TRANS (@lem299453 A n a P R) (@lem299476 A n a P R)). Qed.
Lemma lem299478 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term421 A a P R) = (term454 A a P R).
Proof. exact (fun_ext (fun n : nat => @lem299477 A n a P R)). Qed.
Lemma lem299479 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299480 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term422 A a P R) = (term455 A a P R).
Proof. exact (MK_COMB (@lem299479) (@lem299478 A a P R)). Qed.
Lemma lem299481 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term403 A a P R) = (term455 A a P R).
Proof. exact (TRANS (@lem299427 A a P R) (@lem299480 A a P R)). Qed.
Lemma lem299482 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term366 A a P R) = (term455 A a P R).
Proof. exact (TRANS (@lem299401 A a P R) (@lem299481 A a P R)). Qed.
Lemma lem299483 {A : Type'} (P : type1597 A) (R : type1594 A) : (term367 A P R) = (term456 A P R).
Proof. exact (fun_ext (fun a : A => @lem299482 A a P R)). Qed.
Lemma lem299484 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299485 {A : Type'} (P : type1597 A) (R : type1594 A) : (term368 A P R) = (term457 A P R).
Proof. exact (MK_COMB (@lem299484 A) (@lem299483 A P R)). Qed.
Lemma lem299487 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299488 {A : Type'} (P : type1424 A) : (term458 A P) = (term459 A P).
Proof. exact (@lem299487 A nat P). Qed.
Lemma lem299489 {A : Type'} (P : type1597 A) (R : type1594 A) : (term460 A P R) = (term461 A P R).
Proof. exact (@lem299488 A (term462 A P R)). Qed.
Lemma lem299490 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term463 A P R a) = (term454 A a P R).
Proof. exact (eq_refl (term463 A P R a)). Qed.
Lemma lem299491 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem299492 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (n : nat) : (term464 A P R a n) = (term465 A a P R n).
Proof. exact (MK_COMB (@lem299490 A a P R) (@lem299491 n)). Qed.
Lemma lem299493 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term465 A a P R n) = (term453 A n a P R).
Proof. exact (eq_refl (term465 A a P R n)). Qed.
Lemma lem299494 {A : Type'} (n : nat) (a : A) (P : type1597 A) (R : type1594 A) : (term464 A P R a n) = (term453 A n a P R).
Proof. exact (TRANS (@lem299492 A a P R n) (@lem299493 A n a P R)). Qed.
Lemma lem299495 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term466 A P R a) = (term454 A a P R).
Proof. exact (fun_ext (fun n : nat => @lem299494 A n a P R)). Qed.
Lemma lem299496 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem299497 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term467 A P R a) = (term455 A a P R).
Proof. exact (MK_COMB (@lem299496) (@lem299495 A a P R)). Qed.
Lemma lem299498 {A : Type'} (P : type1597 A) (R : type1594 A) : (term468 A P R) = (term456 A P R).
Proof. exact (fun_ext (fun a : A => @lem299497 A a P R)). Qed.
Lemma lem299499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299500 {A : Type'} (P : type1597 A) (R : type1594 A) : (term460 A P R) = (term457 A P R).
Proof. exact (MK_COMB (@lem299499 A) (@lem299498 A P R)). Qed.
Lemma lem299501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299502 {A : Type'} (P : type1597 A) (R : type1594 A) : (term469 A P R) = (term470 A P R).
Proof. exact (MK_COMB (@lem299501) (@lem299500 A P R)). Qed.
Lemma lem299503 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) : (term463 A P R a) = (term454 A a P R).
Proof. exact (eq_refl (term463 A P R a)). Qed.
Lemma lem299504 {A : Type'} (n : A -> nat) (a : A) : (n a) = (n a).
Proof. exact (eq_refl (n a)). Qed.
Lemma lem299505 {A : Type'} (P : type1597 A) (R : type1594 A) (n : A -> nat) (a : A) : (term471 A P R n a) = (term472 A P R n a).
Proof. exact (MK_COMB (@lem299503 A a P R) (@lem299504 A n a)). Qed.
Lemma lem299506 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) : (term472 A P R n a) = (term473 A n a P R).
Proof. exact (eq_refl (term472 A P R n a)). Qed.
Lemma lem299507 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) : (term471 A P R n a) = (term473 A n a P R).
Proof. exact (TRANS (@lem299505 A P R n a) (@lem299506 A n a P R)). Qed.
Lemma lem299508 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term474 A P R n) = (term475 A n P R).
Proof. exact (fun_ext (fun a : A => @lem299507 A n a P R)). Qed.
Lemma lem299509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299510 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term476 A P R n) = (term477 A n P R).
Proof. exact (MK_COMB (@lem299509 A) (@lem299508 A n P R)). Qed.
Lemma lem299511 {A : Type'} (P : type1597 A) (R : type1594 A) : (term478 A P R) = (term479 A P R).
Proof. exact (fun_ext (fun n : A -> nat => @lem299510 A n P R)). Qed.
Lemma lem299512 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem299513 {A : Type'} (P : type1597 A) (R : type1594 A) : (term461 A P R) = (term480 A P R).
Proof. exact (MK_COMB (@lem299512 A) (@lem299511 A P R)). Qed.
Lemma lem299514 {A : Type'} (P : type1597 A) (R : type1594 A) : ((term460 A P R) = (term461 A P R)) = ((term457 A P R) = (term480 A P R)).
Proof. exact (MK_COMB (@lem299502 A P R) (@lem299513 A P R)). Qed.
Lemma lem299515 {A : Type'} (P : type1597 A) (R : type1594 A) : (term457 A P R) = (term480 A P R).
Proof. exact (EQ_MP (@lem299514 A P R) (@lem299489 A P R)). Qed.
Lemma lem299517 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299518 {A : Type'} (P : type1402 A) : (term142 A P) = (term143 A P).
Proof. exact (@lem299517 A A P). Qed.
Lemma lem299519 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term481 A n P R) = (term482 A n P R).
Proof. exact (@lem299518 A (term483 A n P R)). Qed.
Lemma lem299520 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) : (term484 A n P R a) = (term485 A n a P R).
Proof. exact (eq_refl (term484 A n P R a)). Qed.
Lemma lem299521 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem299522 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) (x : A) : (term486 A n P R a x) = (term487 A n a P R x).
Proof. exact (MK_COMB (@lem299520 A n a P R) (@lem299521 A x)). Qed.
Lemma lem299523 {A : Type'} (n : A -> nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term487 A n a P R x) = (term488 A n x a P R).
Proof. exact (eq_refl (term487 A n a P R x)). Qed.
Lemma lem299524 {A : Type'} (n : A -> nat) (x : A) (a : A) (P : type1597 A) (R : type1594 A) : (term486 A n P R a x) = (term488 A n x a P R).
Proof. exact (TRANS (@lem299522 A n a P R x) (@lem299523 A n x a P R)). Qed.
Lemma lem299525 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) : (term489 A n P R a) = (term485 A n a P R).
Proof. exact (fun_ext (fun x : A => @lem299524 A n x a P R)). Qed.
Lemma lem299526 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem299527 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) : (term490 A n P R a) = (term473 A n a P R).
Proof. exact (MK_COMB (@lem299526 A) (@lem299525 A n a P R)). Qed.
Lemma lem299528 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term491 A n P R) = (term475 A n P R).
Proof. exact (fun_ext (fun a : A => @lem299527 A n a P R)). Qed.
Lemma lem299529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299530 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term481 A n P R) = (term477 A n P R).
Proof. exact (MK_COMB (@lem299529 A) (@lem299528 A n P R)). Qed.
Lemma lem299531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299532 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term492 A n P R) = (term493 A n P R).
Proof. exact (MK_COMB (@lem299531) (@lem299530 A n P R)). Qed.
Lemma lem299533 {A : Type'} (n : A -> nat) (a : A) (P : type1597 A) (R : type1594 A) : (term484 A n P R a) = (term485 A n a P R).
Proof. exact (eq_refl (term484 A n P R a)). Qed.
Lemma lem299534 {A : Type'} (x : A -> A) (a : A) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem299535 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) (x : A -> A) (a : A) : (term494 A n P R x a) = (term495 A n P R x a).
Proof. exact (MK_COMB (@lem299533 A n a P R) (@lem299534 A x a)). Qed.
Lemma lem299536 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) : (term495 A n P R x a) = (term496 A n x a P R).
Proof. exact (eq_refl (term495 A n P R x a)). Qed.
Lemma lem299537 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) : (term494 A n P R x a) = (term496 A n x a P R).
Proof. exact (TRANS (@lem299535 A n P R x a) (@lem299536 A n x a P R)). Qed.
Lemma lem299538 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term497 A n P R x) = (term498 A n x P R).
Proof. exact (fun_ext (fun a : A => @lem299537 A n x a P R)). Qed.
Lemma lem299539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299540 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term499 A n P R x) = (term500 A n x P R).
Proof. exact (MK_COMB (@lem299539 A) (@lem299538 A n x P R)). Qed.
Lemma lem299541 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term501 A n P R) = (term502 A n P R).
Proof. exact (fun_ext (fun x : A -> A => @lem299540 A n x P R)). Qed.
Lemma lem299542 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem299543 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term482 A n P R) = (term503 A n P R).
Proof. exact (MK_COMB (@lem299542 A) (@lem299541 A n P R)). Qed.
Lemma lem299544 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : ((term481 A n P R) = (term482 A n P R)) = ((term477 A n P R) = (term503 A n P R)).
Proof. exact (MK_COMB (@lem299532 A n P R) (@lem299543 A n P R)). Qed.
Lemma lem299545 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term477 A n P R) = (term503 A n P R).
Proof. exact (EQ_MP (@lem299544 A n P R) (@lem299519 A n P R)). Qed.
Lemma lem299547 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299548 {A : Type'} (P : type1382 A) : (term504 A P) = (term505 A P).
Proof. exact (@lem299547 A (nat -> A) P). Qed.
Lemma lem299549 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term506 A n x P R) = (term507 A n x P R).
Proof. exact (@lem299548 A (term508 A n x P R)). Qed.
Lemma lem299550 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) : (term509 A n x P R a) = (term510 A n x a P R).
Proof. exact (eq_refl (term509 A n x P R a)). Qed.
Lemma lem299551 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem299552 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term511 A n x P R a f) = (term512 A n x a P R f).
Proof. exact (MK_COMB (@lem299550 A n x a P R) (@lem299551 A f)). Qed.
Lemma lem299553 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term512 A n x a P R f) = (term513 A n x a P R f).
Proof. exact (eq_refl (term512 A n x a P R f)). Qed.
Lemma lem299554 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) (f : nat -> A) : (term511 A n x P R a f) = (term513 A n x a P R f).
Proof. exact (TRANS (@lem299552 A n x a P R f) (@lem299553 A n x a P R f)). Qed.
Lemma lem299555 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) : (term514 A n x P R a) = (term510 A n x a P R).
Proof. exact (fun_ext (fun f : nat -> A => @lem299554 A n x a P R f)). Qed.
Lemma lem299556 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem299557 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) : (term515 A n x P R a) = (term496 A n x a P R).
Proof. exact (MK_COMB (@lem299556 A) (@lem299555 A n x a P R)). Qed.
Lemma lem299558 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term516 A n x P R) = (term498 A n x P R).
Proof. exact (fun_ext (fun a : A => @lem299557 A n x a P R)). Qed.
Lemma lem299559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299560 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term506 A n x P R) = (term500 A n x P R).
Proof. exact (MK_COMB (@lem299559 A) (@lem299558 A n x P R)). Qed.
Lemma lem299561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299562 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term517 A n x P R) = (term518 A n x P R).
Proof. exact (MK_COMB (@lem299561) (@lem299560 A n x P R)). Qed.
Lemma lem299563 {A : Type'} (n : A -> nat) (x : A -> A) (a : A) (P : type1597 A) (R : type1594 A) : (term509 A n x P R a) = (term510 A n x a P R).
Proof. exact (eq_refl (term509 A n x P R a)). Qed.
Lemma lem299564 {A : Type'} (f : type1423 A) (a : A) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem299565 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) (f : type1423 A) (a : A) : (term519 A n x P R f a) = (term520 A n x P R f a).
Proof. exact (MK_COMB (@lem299563 A n x a P R) (@lem299564 A f a)). Qed.
Lemma lem299566 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) (f : type1423 A) (a : A) : (term520 A n x P R f a) = (term521 A n x P R f a).
Proof. exact (eq_refl (term520 A n x P R f a)). Qed.
Lemma lem299567 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) (f : type1423 A) (a : A) : (term519 A n x P R f a) = (term521 A n x P R f a).
Proof. exact (TRANS (@lem299565 A n x P R f a) (@lem299566 A n x P R f a)). Qed.
Lemma lem299568 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) (f : type1423 A) : (term522 A n x P R f) = (term523 A n x P R f).
Proof. exact (fun_ext (fun a : A => @lem299567 A n x P R f a)). Qed.
Lemma lem299569 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem299570 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) (f : type1423 A) : (term524 A n x P R f) = (term525 A n x P R f).
Proof. exact (MK_COMB (@lem299569 A) (@lem299568 A n x P R f)). Qed.
Lemma lem299571 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term526 A n x P R) = (term527 A n x P R).
Proof. exact (fun_ext (fun f : type1423 A => @lem299570 A n x P R f)). Qed.
Lemma lem299572 {A : Type'} : (@ex (A -> nat -> A)) = (@ex (A -> nat -> A)).
Proof. exact (eq_refl (@ex (A -> nat -> A))). Qed.
Lemma lem299573 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term507 A n x P R) = (term528 A n x P R).
Proof. exact (MK_COMB (@lem299572 A) (@lem299571 A n x P R)). Qed.
Lemma lem299574 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : ((term506 A n x P R) = (term507 A n x P R)) = ((term500 A n x P R) = (term528 A n x P R)).
Proof. exact (MK_COMB (@lem299562 A n x P R) (@lem299573 A n x P R)). Qed.
Lemma lem299575 {A : Type'} (n : A -> nat) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term500 A n x P R) = (term528 A n x P R).
Proof. exact (EQ_MP (@lem299574 A n x P R) (@lem299549 A n x P R)). Qed.
Lemma lem299576 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term502 A n P R) = (term529 A n P R).
Proof. exact (fun_ext (fun x : A -> A => @lem299575 A n x P R)). Qed.
Lemma lem299577 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem299578 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term503 A n P R) = (term530 A n P R).
Proof. exact (MK_COMB (@lem299577 A) (@lem299576 A n P R)). Qed.
Lemma lem299579 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term477 A n P R) = (term530 A n P R).
Proof. exact (TRANS (@lem299545 A n P R) (@lem299578 A n P R)). Qed.
Lemma lem299580 {A : Type'} (P : type1597 A) (R : type1594 A) : (term479 A P R) = (term531 A P R).
Proof. exact (fun_ext (fun n : A -> nat => @lem299579 A n P R)). Qed.
Lemma lem299581 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem299582 {A : Type'} (P : type1597 A) (R : type1594 A) : (term480 A P R) = (term532 A P R).
Proof. exact (MK_COMB (@lem299581 A) (@lem299580 A P R)). Qed.
Lemma lem299583 {A : Type'} (P : type1597 A) (R : type1594 A) : (term457 A P R) = (term532 A P R).
Proof. exact (TRANS (@lem299515 A P R) (@lem299582 A P R)). Qed.
Lemma lem299584 {A : Type'} (P : type1597 A) (R : type1594 A) : (term368 A P R) = (term532 A P R).
Proof. exact (TRANS (@lem299485 A P R) (@lem299583 A P R)). Qed.
Lemma lem299585 {A : Type'} (P : type1597 A) : (term369 A P) = (term533 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299584 A P R)). Qed.
Lemma lem299586 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299587 {A : Type'} (P : type1597 A) : (term370 A P) = (term534 A P).
Proof. exact (MK_COMB (@lem299586 A) (@lem299585 A P)). Qed.
Lemma lem299589 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299590 {A : Type'} (P : type932 A) : (term535 A P) = (term536 A P).
Proof. exact (@lem299589 (type1594 A) (A -> nat) P). Qed.
Lemma lem299591 {A : Type'} (P : type1597 A) : (term537 A P) = (term538 A P).
Proof. exact (@lem299590 A (term539 A P)). Qed.
Lemma lem299592 {A : Type'} (P : type1597 A) (R : type1594 A) : (term540 A P R) = (term531 A P R).
Proof. exact (eq_refl (term540 A P R)). Qed.
Lemma lem299593 {A : Type'} (n : A -> nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem299594 {A : Type'} (P : type1597 A) (R : type1594 A) (n : A -> nat) : (term541 A P R n) = (term542 A P R n).
Proof. exact (MK_COMB (@lem299592 A P R) (@lem299593 A n)). Qed.
Lemma lem299595 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term542 A P R n) = (term530 A n P R).
Proof. exact (eq_refl (term542 A P R n)). Qed.
Lemma lem299596 {A : Type'} (n : A -> nat) (P : type1597 A) (R : type1594 A) : (term541 A P R n) = (term530 A n P R).
Proof. exact (TRANS (@lem299594 A P R n) (@lem299595 A n P R)). Qed.
Lemma lem299597 {A : Type'} (P : type1597 A) (R : type1594 A) : (term543 A P R) = (term531 A P R).
Proof. exact (fun_ext (fun n : A -> nat => @lem299596 A n P R)). Qed.
Lemma lem299598 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem299599 {A : Type'} (P : type1597 A) (R : type1594 A) : (term544 A P R) = (term532 A P R).
Proof. exact (MK_COMB (@lem299598 A) (@lem299597 A P R)). Qed.
Lemma lem299600 {A : Type'} (P : type1597 A) : (term545 A P) = (term533 A P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299599 A P R)). Qed.
Lemma lem299601 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299602 {A : Type'} (P : type1597 A) : (term537 A P) = (term534 A P).
Proof. exact (MK_COMB (@lem299601 A) (@lem299600 A P)). Qed.
Lemma lem299603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299604 {A : Type'} (P : type1597 A) : (term546 A P) = (term547 A P).
Proof. exact (MK_COMB (@lem299603) (@lem299602 A P)). Qed.
Lemma lem299605 {A : Type'} (P : type1597 A) (R : type1594 A) : (term540 A P R) = (term531 A P R).
Proof. exact (eq_refl (term540 A P R)). Qed.
Lemma lem299606 {A : Type'} (n : type936 A) (R : type1594 A) : (n R) = (n R).
Proof. exact (eq_refl (n R)). Qed.
Lemma lem299607 {A : Type'} (P : type1597 A) (n : type936 A) (R : type1594 A) : (term548 A P n R) = (term549 A P n R).
Proof. exact (MK_COMB (@lem299605 A P R) (@lem299606 A n R)). Qed.
Lemma lem299608 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) : (term549 A P n R) = (term550 A n P R).
Proof. exact (eq_refl (term549 A P n R)). Qed.
Lemma lem299609 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) : (term548 A P n R) = (term550 A n P R).
Proof. exact (TRANS (@lem299607 A P n R) (@lem299608 A n P R)). Qed.
Lemma lem299610 {A : Type'} (n : type936 A) (P : type1597 A) : (term551 A P n) = (term552 A n P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299609 A n P R)). Qed.
Lemma lem299611 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299612 {A : Type'} (n : type936 A) (P : type1597 A) : (term553 A P n) = (term554 A n P).
Proof. exact (MK_COMB (@lem299611 A) (@lem299610 A n P)). Qed.
Lemma lem299613 {A : Type'} (P : type1597 A) : (term555 A P) = (term556 A P).
Proof. exact (fun_ext (fun n : type936 A => @lem299612 A n P)). Qed.
Lemma lem299614 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> nat)) = (@ex ((nat -> A -> A -> Prop) -> A -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> nat))). Qed.
Lemma lem299615 {A : Type'} (P : type1597 A) : (term538 A P) = (term557 A P).
Proof. exact (MK_COMB (@lem299614 A) (@lem299613 A P)). Qed.
Lemma lem299616 {A : Type'} (P : type1597 A) : ((term537 A P) = (term538 A P)) = ((term534 A P) = (term557 A P)).
Proof. exact (MK_COMB (@lem299604 A P) (@lem299615 A P)). Qed.
Lemma lem299617 {A : Type'} (P : type1597 A) : (term534 A P) = (term557 A P).
Proof. exact (EQ_MP (@lem299616 A P) (@lem299591 A P)). Qed.
Lemma lem299619 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299620 {A : Type'} (P : type931 A) : (term558 A P) = (term559 A P).
Proof. exact (@lem299619 (type1594 A) (A -> A) P). Qed.
Lemma lem299621 {A : Type'} (n : type936 A) (P : type1597 A) : (term560 A n P) = (term561 A n P).
Proof. exact (@lem299620 A (term562 A n P)). Qed.
Lemma lem299622 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) : (term563 A n P R) = (term564 A n P R).
Proof. exact (eq_refl (term563 A n P R)). Qed.
Lemma lem299623 {A : Type'} (x : A -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem299624 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) (x : A -> A) : (term565 A n P R x) = (term566 A n P R x).
Proof. exact (MK_COMB (@lem299622 A n P R) (@lem299623 A x)). Qed.
Lemma lem299625 {A : Type'} (n : type936 A) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term566 A n P R x) = (term567 A n x P R).
Proof. exact (eq_refl (term566 A n P R x)). Qed.
Lemma lem299626 {A : Type'} (n : type936 A) (x : A -> A) (P : type1597 A) (R : type1594 A) : (term565 A n P R x) = (term567 A n x P R).
Proof. exact (TRANS (@lem299624 A n P R x) (@lem299625 A n x P R)). Qed.
Lemma lem299627 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) : (term568 A n P R) = (term564 A n P R).
Proof. exact (fun_ext (fun x : A -> A => @lem299626 A n x P R)). Qed.
Lemma lem299628 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem299629 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) : (term569 A n P R) = (term550 A n P R).
Proof. exact (MK_COMB (@lem299628 A) (@lem299627 A n P R)). Qed.
Lemma lem299630 {A : Type'} (n : type936 A) (P : type1597 A) : (term570 A n P) = (term552 A n P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299629 A n P R)). Qed.
Lemma lem299631 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299632 {A : Type'} (n : type936 A) (P : type1597 A) : (term560 A n P) = (term554 A n P).
Proof. exact (MK_COMB (@lem299631 A) (@lem299630 A n P)). Qed.
Lemma lem299633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299634 {A : Type'} (n : type936 A) (P : type1597 A) : (term571 A n P) = (term572 A n P).
Proof. exact (MK_COMB (@lem299633) (@lem299632 A n P)). Qed.
Lemma lem299635 {A : Type'} (n : type936 A) (P : type1597 A) (R : type1594 A) : (term563 A n P R) = (term564 A n P R).
Proof. exact (eq_refl (term563 A n P R)). Qed.
Lemma lem299636 {A : Type'} (x : type935 A) (R : type1594 A) : (x R) = (x R).
Proof. exact (eq_refl (x R)). Qed.
Lemma lem299637 {A : Type'} (n : type936 A) (P : type1597 A) (x : type935 A) (R : type1594 A) : (term573 A n P x R) = (term574 A n P x R).
Proof. exact (MK_COMB (@lem299635 A n P R) (@lem299636 A x R)). Qed.
Lemma lem299638 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) : (term574 A n P x R) = (term575 A n x P R).
Proof. exact (eq_refl (term574 A n P x R)). Qed.
Lemma lem299639 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) : (term573 A n P x R) = (term575 A n x P R).
Proof. exact (TRANS (@lem299637 A n P x R) (@lem299638 A n x P R)). Qed.
Lemma lem299640 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term576 A n P x) = (term577 A n x P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299639 A n x P R)). Qed.
Lemma lem299641 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299642 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term578 A n P x) = (term579 A n x P).
Proof. exact (MK_COMB (@lem299641 A) (@lem299640 A n x P)). Qed.
Lemma lem299643 {A : Type'} (n : type936 A) (P : type1597 A) : (term580 A n P) = (term581 A n P).
Proof. exact (fun_ext (fun x : type935 A => @lem299642 A n x P)). Qed.
Lemma lem299644 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> A)) = (@ex ((nat -> A -> A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> A))). Qed.
Lemma lem299645 {A : Type'} (n : type936 A) (P : type1597 A) : (term561 A n P) = (term582 A n P).
Proof. exact (MK_COMB (@lem299644 A) (@lem299643 A n P)). Qed.
Lemma lem299646 {A : Type'} (n : type936 A) (P : type1597 A) : ((term560 A n P) = (term561 A n P)) = ((term554 A n P) = (term582 A n P)).
Proof. exact (MK_COMB (@lem299634 A n P) (@lem299645 A n P)). Qed.
Lemma lem299647 {A : Type'} (n : type936 A) (P : type1597 A) : (term554 A n P) = (term582 A n P).
Proof. exact (EQ_MP (@lem299646 A n P) (@lem299621 A n P)). Qed.
Lemma lem299649 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299650 {A : Type'} (P : type930 A) : (term583 A P) = (term584 A P).
Proof. exact (@lem299649 (type1594 A) (type1423 A) P). Qed.
Lemma lem299651 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term585 A n x P) = (term586 A n x P).
Proof. exact (@lem299650 A (term587 A n x P)). Qed.
Lemma lem299652 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) : (term588 A n x P R) = (term589 A n x P R).
Proof. exact (eq_refl (term588 A n x P R)). Qed.
Lemma lem299653 {A : Type'} (f : type1423 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem299654 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) (f : type1423 A) : (term590 A n x P R f) = (term591 A n x P R f).
Proof. exact (MK_COMB (@lem299652 A n x P R) (@lem299653 A f)). Qed.
Lemma lem299655 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) (f : type1423 A) : (term591 A n x P R f) = (term592 A n x P R f).
Proof. exact (eq_refl (term591 A n x P R f)). Qed.
Lemma lem299656 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) (f : type1423 A) : (term590 A n x P R f) = (term592 A n x P R f).
Proof. exact (TRANS (@lem299654 A n x P R f) (@lem299655 A n x P R f)). Qed.
Lemma lem299657 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) : (term593 A n x P R) = (term589 A n x P R).
Proof. exact (fun_ext (fun f : type1423 A => @lem299656 A n x P R f)). Qed.
Lemma lem299658 {A : Type'} : (@ex (A -> nat -> A)) = (@ex (A -> nat -> A)).
Proof. exact (eq_refl (@ex (A -> nat -> A))). Qed.
Lemma lem299659 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) : (term594 A n x P R) = (term575 A n x P R).
Proof. exact (MK_COMB (@lem299658 A) (@lem299657 A n x P R)). Qed.
Lemma lem299660 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term595 A n x P) = (term577 A n x P).
Proof. exact (fun_ext (fun R : type1594 A => @lem299659 A n x P R)). Qed.
Lemma lem299661 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299662 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term585 A n x P) = (term579 A n x P).
Proof. exact (MK_COMB (@lem299661 A) (@lem299660 A n x P)). Qed.
Lemma lem299663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299664 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term596 A n x P) = (term597 A n x P).
Proof. exact (MK_COMB (@lem299663) (@lem299662 A n x P)). Qed.
Lemma lem299665 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (R : type1594 A) : (term588 A n x P R) = (term589 A n x P R).
Proof. exact (eq_refl (term588 A n x P R)). Qed.
Lemma lem299666 {A : Type'} (f : type934 A) (R : type1594 A) : (f R) = (f R).
Proof. exact (eq_refl (f R)). Qed.
Lemma lem299667 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (f : type934 A) (R : type1594 A) : (term598 A n x P f R) = (term599 A n x P f R).
Proof. exact (MK_COMB (@lem299665 A n x P R) (@lem299666 A f R)). Qed.
Lemma lem299668 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (f : type934 A) (R : type1594 A) : (term599 A n x P f R) = (term600 A n x P f R).
Proof. exact (eq_refl (term599 A n x P f R)). Qed.
Lemma lem299669 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (f : type934 A) (R : type1594 A) : (term598 A n x P f R) = (term600 A n x P f R).
Proof. exact (TRANS (@lem299667 A n x P f R) (@lem299668 A n x P f R)). Qed.
Lemma lem299670 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (f : type934 A) : (term601 A n x P f) = (term602 A n x P f).
Proof. exact (fun_ext (fun R : type1594 A => @lem299669 A n x P f R)). Qed.
Lemma lem299671 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem299672 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) (f : type934 A) : (term603 A n x P f) = (term604 A n x P f).
Proof. exact (MK_COMB (@lem299671 A) (@lem299670 A n x P f)). Qed.
Lemma lem299673 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term605 A n x P) = (term606 A n x P).
Proof. exact (fun_ext (fun f : type934 A => @lem299672 A n x P f)). Qed.
Lemma lem299674 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> nat -> A)) = (@ex ((nat -> A -> A -> Prop) -> A -> nat -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> nat -> A))). Qed.
Lemma lem299675 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term586 A n x P) = (term607 A n x P).
Proof. exact (MK_COMB (@lem299674 A) (@lem299673 A n x P)). Qed.
Lemma lem299676 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : ((term585 A n x P) = (term586 A n x P)) = ((term579 A n x P) = (term607 A n x P)).
Proof. exact (MK_COMB (@lem299664 A n x P) (@lem299675 A n x P)). Qed.
Lemma lem299677 {A : Type'} (n : type936 A) (x : type935 A) (P : type1597 A) : (term579 A n x P) = (term607 A n x P).
Proof. exact (EQ_MP (@lem299676 A n x P) (@lem299651 A n x P)). Qed.
Lemma lem299678 {A : Type'} (n : type936 A) (P : type1597 A) : (term581 A n P) = (term608 A n P).
Proof. exact (fun_ext (fun x : type935 A => @lem299677 A n x P)). Qed.
Lemma lem299679 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> A)) = (@ex ((nat -> A -> A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> A))). Qed.
Lemma lem299680 {A : Type'} (n : type936 A) (P : type1597 A) : (term582 A n P) = (term609 A n P).
Proof. exact (MK_COMB (@lem299679 A) (@lem299678 A n P)). Qed.
Lemma lem299681 {A : Type'} (n : type936 A) (P : type1597 A) : (term554 A n P) = (term609 A n P).
Proof. exact (TRANS (@lem299647 A n P) (@lem299680 A n P)). Qed.
Lemma lem299682 {A : Type'} (P : type1597 A) : (term556 A P) = (term610 A P).
Proof. exact (fun_ext (fun n : type936 A => @lem299681 A n P)). Qed.
Lemma lem299683 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> nat)) = (@ex ((nat -> A -> A -> Prop) -> A -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> nat))). Qed.
Lemma lem299684 {A : Type'} (P : type1597 A) : (term557 A P) = (term611 A P).
Proof. exact (MK_COMB (@lem299683 A) (@lem299682 A P)). Qed.
Lemma lem299685 {A : Type'} (P : type1597 A) : (term534 A P) = (term611 A P).
Proof. exact (TRANS (@lem299617 A P) (@lem299684 A P)). Qed.
Lemma lem299686 {A : Type'} (P : type1597 A) : (term370 A P) = (term611 A P).
Proof. exact (TRANS (@lem299587 A P) (@lem299685 A P)). Qed.
Lemma lem299687 {A : Type'} : (term371 A) = (term612 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem299686 A P)). Qed.
Lemma lem299688 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299689 {A : Type'} : (term372 A) = (term613 A).
Proof. exact (MK_COMB (@lem299688 A) (@lem299687 A)). Qed.
Lemma lem299691 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299692 {A : Type'} (P : type941 A) : (term614 A P) = (term615 A P).
Proof. exact (@lem299691 (type1597 A) (type936 A) P). Qed.
Lemma lem299693 {A : Type'} : (term616 A) = (term617 A).
Proof. exact (@lem299692 A (term618 A)). Qed.
Lemma lem299694 {A : Type'} (P : type1597 A) : (term619 A P) = (term610 A P).
Proof. exact (eq_refl (term619 A P)). Qed.
Lemma lem299695 {A : Type'} (n : type936 A) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem299696 {A : Type'} (P : type1597 A) (n : type936 A) : (term620 A P n) = (term621 A P n).
Proof. exact (MK_COMB (@lem299694 A P) (@lem299695 A n)). Qed.
Lemma lem299697 {A : Type'} (n : type936 A) (P : type1597 A) : (term621 A P n) = (term609 A n P).
Proof. exact (eq_refl (term621 A P n)). Qed.
Lemma lem299698 {A : Type'} (n : type936 A) (P : type1597 A) : (term620 A P n) = (term609 A n P).
Proof. exact (TRANS (@lem299696 A P n) (@lem299697 A n P)). Qed.
Lemma lem299699 {A : Type'} (P : type1597 A) : (term622 A P) = (term610 A P).
Proof. exact (fun_ext (fun n : type936 A => @lem299698 A n P)). Qed.
Lemma lem299700 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> nat)) = (@ex ((nat -> A -> A -> Prop) -> A -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> nat))). Qed.
Lemma lem299701 {A : Type'} (P : type1597 A) : (term623 A P) = (term611 A P).
Proof. exact (MK_COMB (@lem299700 A) (@lem299699 A P)). Qed.
Lemma lem299702 {A : Type'} : (term624 A) = (term612 A).
Proof. exact (fun_ext (fun P : type1597 A => @lem299701 A P)). Qed.
Lemma lem299703 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299704 {A : Type'} : (term616 A) = (term613 A).
Proof. exact (MK_COMB (@lem299703 A) (@lem299702 A)). Qed.
Lemma lem299705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299706 {A : Type'} : (term625 A) = (term626 A).
Proof. exact (MK_COMB (@lem299705) (@lem299704 A)). Qed.
Lemma lem299707 {A : Type'} (P : type1597 A) : (term619 A P) = (term610 A P).
Proof. exact (eq_refl (term619 A P)). Qed.
Lemma lem299708 {A : Type'} (n : type946 A) (P : type1597 A) : (n P) = (n P).
Proof. exact (eq_refl (n P)). Qed.
Lemma lem299709 {A : Type'} (n : type946 A) (P : type1597 A) : (term627 A n P) = (term628 A n P).
Proof. exact (MK_COMB (@lem299707 A P) (@lem299708 A n P)). Qed.
Lemma lem299710 {A : Type'} (n : type946 A) (P : type1597 A) : (term628 A n P) = (term629 A n P).
Proof. exact (eq_refl (term628 A n P)). Qed.
Lemma lem299711 {A : Type'} (n : type946 A) (P : type1597 A) : (term627 A n P) = (term629 A n P).
Proof. exact (TRANS (@lem299709 A n P) (@lem299710 A n P)). Qed.
Lemma lem299712 {A : Type'} (n : type946 A) : (term630 A n) = (term631 A n).
Proof. exact (fun_ext (fun P : type1597 A => @lem299711 A n P)). Qed.
Lemma lem299713 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299714 {A : Type'} (n : type946 A) : (term632 A n) = (term633 A n).
Proof. exact (MK_COMB (@lem299713 A) (@lem299712 A n)). Qed.
Lemma lem299715 {A : Type'} : (term634 A) = (term635 A).
Proof. exact (fun_ext (fun n : type946 A => @lem299714 A n)). Qed.
Lemma lem299716 {A : Type'} : (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat)) = (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat))). Qed.
Lemma lem299717 {A : Type'} : (term617 A) = (term636 A).
Proof. exact (MK_COMB (@lem299716 A) (@lem299715 A)). Qed.
Lemma lem299718 {A : Type'} : ((term616 A) = (term617 A)) = ((term613 A) = (term636 A)).
Proof. exact (MK_COMB (@lem299706 A) (@lem299717 A)). Qed.
Lemma lem299719 {A : Type'} : (term613 A) = (term636 A).
Proof. exact (EQ_MP (@lem299718 A) (@lem299693 A)). Qed.
Lemma lem299721 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299722 {A : Type'} (P : type940 A) : (term637 A P) = (term638 A P).
Proof. exact (@lem299721 (type1597 A) (type935 A) P). Qed.
Lemma lem299723 {A : Type'} (n : type946 A) : (term639 A n) = (term640 A n).
Proof. exact (@lem299722 A (term641 A n)). Qed.
Lemma lem299724 {A : Type'} (n : type946 A) (P : type1597 A) : (term642 A n P) = (term643 A n P).
Proof. exact (eq_refl (term642 A n P)). Qed.
Lemma lem299725 {A : Type'} (x : type935 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem299726 {A : Type'} (n : type946 A) (P : type1597 A) (x : type935 A) : (term644 A n P x) = (term645 A n P x).
Proof. exact (MK_COMB (@lem299724 A n P) (@lem299725 A x)). Qed.
Lemma lem299727 {A : Type'} (n : type946 A) (x : type935 A) (P : type1597 A) : (term645 A n P x) = (term646 A n x P).
Proof. exact (eq_refl (term645 A n P x)). Qed.
Lemma lem299728 {A : Type'} (n : type946 A) (x : type935 A) (P : type1597 A) : (term644 A n P x) = (term646 A n x P).
Proof. exact (TRANS (@lem299726 A n P x) (@lem299727 A n x P)). Qed.
Lemma lem299729 {A : Type'} (n : type946 A) (P : type1597 A) : (term647 A n P) = (term643 A n P).
Proof. exact (fun_ext (fun x : type935 A => @lem299728 A n x P)). Qed.
Lemma lem299730 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> A)) = (@ex ((nat -> A -> A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> A))). Qed.
Lemma lem299731 {A : Type'} (n : type946 A) (P : type1597 A) : (term648 A n P) = (term629 A n P).
Proof. exact (MK_COMB (@lem299730 A) (@lem299729 A n P)). Qed.
Lemma lem299732 {A : Type'} (n : type946 A) : (term649 A n) = (term631 A n).
Proof. exact (fun_ext (fun P : type1597 A => @lem299731 A n P)). Qed.
Lemma lem299733 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299734 {A : Type'} (n : type946 A) : (term639 A n) = (term633 A n).
Proof. exact (MK_COMB (@lem299733 A) (@lem299732 A n)). Qed.
Lemma lem299735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299736 {A : Type'} (n : type946 A) : (term650 A n) = (term651 A n).
Proof. exact (MK_COMB (@lem299735) (@lem299734 A n)). Qed.
Lemma lem299737 {A : Type'} (n : type946 A) (P : type1597 A) : (term642 A n P) = (term643 A n P).
Proof. exact (eq_refl (term642 A n P)). Qed.
Lemma lem299738 {A : Type'} (x : type945 A) (P : type1597 A) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem299739 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term652 A n x P) = (term653 A n x P).
Proof. exact (MK_COMB (@lem299737 A n P) (@lem299738 A x P)). Qed.
Lemma lem299740 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term653 A n x P) = (term654 A n x P).
Proof. exact (eq_refl (term653 A n x P)). Qed.
Lemma lem299741 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term652 A n x P) = (term654 A n x P).
Proof. exact (TRANS (@lem299739 A n x P) (@lem299740 A n x P)). Qed.
Lemma lem299742 {A : Type'} (n : type946 A) (x : type945 A) : (term655 A n x) = (term656 A n x).
Proof. exact (fun_ext (fun P : type1597 A => @lem299741 A n x P)). Qed.
Lemma lem299743 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299744 {A : Type'} (n : type946 A) (x : type945 A) : (term657 A n x) = (term658 A n x).
Proof. exact (MK_COMB (@lem299743 A) (@lem299742 A n x)). Qed.
Lemma lem299745 {A : Type'} (n : type946 A) : (term659 A n) = (term660 A n).
Proof. exact (fun_ext (fun x : type945 A => @lem299744 A n x)). Qed.
Lemma lem299746 {A : Type'} : (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A)) = (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A))). Qed.
Lemma lem299747 {A : Type'} (n : type946 A) : (term640 A n) = (term661 A n).
Proof. exact (MK_COMB (@lem299746 A) (@lem299745 A n)). Qed.
Lemma lem299748 {A : Type'} (n : type946 A) : ((term639 A n) = (term640 A n)) = ((term633 A n) = (term661 A n)).
Proof. exact (MK_COMB (@lem299736 A n) (@lem299747 A n)). Qed.
Lemma lem299749 {A : Type'} (n : type946 A) : (term633 A n) = (term661 A n).
Proof. exact (EQ_MP (@lem299748 A n) (@lem299723 A n)). Qed.
Lemma lem299751 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem299752 {A : Type'} (P : type939 A) : (term662 A P) = (term663 A P).
Proof. exact (@lem299751 (type1597 A) (type934 A) P). Qed.
Lemma lem299753 {A : Type'} (n : type946 A) (x : type945 A) : (term664 A n x) = (term665 A n x).
Proof. exact (@lem299752 A (term666 A n x)). Qed.
Lemma lem299754 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term667 A n x P) = (term668 A n x P).
Proof. exact (eq_refl (term667 A n x P)). Qed.
Lemma lem299755 {A : Type'} (f : type934 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem299756 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (f : type934 A) : (term669 A n x P f) = (term670 A n x P f).
Proof. exact (MK_COMB (@lem299754 A n x P) (@lem299755 A f)). Qed.
Lemma lem299757 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (f : type934 A) : (term670 A n x P f) = (term671 A n x P f).
Proof. exact (eq_refl (term670 A n x P f)). Qed.
Lemma lem299758 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (f : type934 A) : (term669 A n x P f) = (term671 A n x P f).
Proof. exact (TRANS (@lem299756 A n x P f) (@lem299757 A n x P f)). Qed.
Lemma lem299759 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term672 A n x P) = (term668 A n x P).
Proof. exact (fun_ext (fun f : type934 A => @lem299758 A n x P f)). Qed.
Lemma lem299760 {A : Type'} : (@ex ((nat -> A -> A -> Prop) -> A -> nat -> A)) = (@ex ((nat -> A -> A -> Prop) -> A -> nat -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> A -> Prop) -> A -> nat -> A))). Qed.
Lemma lem299761 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term673 A n x P) = (term654 A n x P).
Proof. exact (MK_COMB (@lem299760 A) (@lem299759 A n x P)). Qed.
Lemma lem299762 {A : Type'} (n : type946 A) (x : type945 A) : (term674 A n x) = (term656 A n x).
Proof. exact (fun_ext (fun P : type1597 A => @lem299761 A n x P)). Qed.
Lemma lem299763 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299764 {A : Type'} (n : type946 A) (x : type945 A) : (term664 A n x) = (term658 A n x).
Proof. exact (MK_COMB (@lem299763 A) (@lem299762 A n x)). Qed.
Lemma lem299765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem299766 {A : Type'} (n : type946 A) (x : type945 A) : (term675 A n x) = (term676 A n x).
Proof. exact (MK_COMB (@lem299765) (@lem299764 A n x)). Qed.
Lemma lem299767 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) : (term667 A n x P) = (term668 A n x P).
Proof. exact (eq_refl (term667 A n x P)). Qed.
Lemma lem299768 {A : Type'} (f : type944 A) (P : type1597 A) : (f P) = (f P).
Proof. exact (eq_refl (f P)). Qed.
Lemma lem299769 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term677 A n x f P) = (term678 A n x f P).
Proof. exact (MK_COMB (@lem299767 A n x P) (@lem299768 A f P)). Qed.
Lemma lem299770 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term678 A n x f P) = (term679 A n x f P).
Proof. exact (eq_refl (term678 A n x f P)). Qed.
Lemma lem299771 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term677 A n x f P) = (term679 A n x f P).
Proof. exact (TRANS (@lem299769 A n x f P) (@lem299770 A n x f P)). Qed.
Lemma lem299772 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term680 A n x f) = (term681 A n x f).
Proof. exact (fun_ext (fun P : type1597 A => @lem299771 A n x f P)). Qed.
Lemma lem299773 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem299774 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term682 A n x f) = (term683 A n x f).
Proof. exact (MK_COMB (@lem299773 A) (@lem299772 A n x f)). Qed.
Lemma lem299775 {A : Type'} (n : type946 A) (x : type945 A) : (term684 A n x) = (term685 A n x).
Proof. exact (fun_ext (fun f : type944 A => @lem299774 A n x f)). Qed.
Lemma lem299776 {A : Type'} : (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A)) = (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A))). Qed.
Lemma lem299777 {A : Type'} (n : type946 A) (x : type945 A) : (term665 A n x) = (term686 A n x).
Proof. exact (MK_COMB (@lem299776 A) (@lem299775 A n x)). Qed.
Lemma lem299778 {A : Type'} (n : type946 A) (x : type945 A) : ((term664 A n x) = (term665 A n x)) = ((term658 A n x) = (term686 A n x)).
Proof. exact (MK_COMB (@lem299766 A n x) (@lem299777 A n x)). Qed.
Lemma lem299779 {A : Type'} (n : type946 A) (x : type945 A) : (term658 A n x) = (term686 A n x).
Proof. exact (EQ_MP (@lem299778 A n x) (@lem299753 A n x)). Qed.
Lemma lem299780 {A : Type'} (n : type946 A) : (term660 A n) = (term687 A n).
Proof. exact (fun_ext (fun x : type945 A => @lem299779 A n x)). Qed.
Lemma lem299781 {A : Type'} : (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A)) = (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A))). Qed.
Lemma lem299782 {A : Type'} (n : type946 A) : (term661 A n) = (term688 A n).
Proof. exact (MK_COMB (@lem299781 A) (@lem299780 A n)). Qed.
Lemma lem299783 {A : Type'} (n : type946 A) : (term633 A n) = (term688 A n).
Proof. exact (TRANS (@lem299749 A n) (@lem299782 A n)). Qed.
Lemma lem299784 {A : Type'} : (term635 A) = (term689 A).
Proof. exact (fun_ext (fun n : type946 A => @lem299783 A n)). Qed.
Lemma lem299785 {A : Type'} : (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat)) = (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat))). Qed.
Lemma lem299786 {A : Type'} : (term636 A) = (term690 A).
Proof. exact (MK_COMB (@lem299785 A) (@lem299784 A)). Qed.
Lemma lem299787 {A : Type'} : (term613 A) = (term690 A).
Proof. exact (TRANS (@lem299719 A) (@lem299786 A)). Qed.
Lemma lem299789 {A : Type'} : (term372 A) = (term690 A).
Proof. exact (TRANS (@lem299689 A) (@lem299787 A)). Qed.
Lemma lem299790 {A : Type'} : (term17 A) = (term690 A).
Proof. exact (TRANS (@lem299140 A) (@lem299789 A)). Qed.
Lemma lem299791 {A : Type'} (h1 : term17 A) : term690 A.
Proof. exact (EQ_MP (@lem299790 A) (@lem298468 A h1)). Qed.
Lemma lem299792 {A : Type'} (n : type946 A) (h1 : term688 A n) : term688 A n.
Proof. exact (h1). Qed.
Lemma lem299793 {A : Type'} (n : type946 A) (x : type945 A) (h1 : term686 A n x) : term686 A n x.
Proof. exact (h1). Qed.
Lemma lem299794 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term683 A n x f.
Proof. exact (h1). Qed.
Lemma lem299795 {A : Type'} (P : type1597 A) (h1 : term325 A P) : term325 A P.
Proof. exact (h1). Qed.
Lemma lem299796 {A : Type'} (P : type1597 A) (R : type1594 A) (h1 : term323 A P R) : term323 A P R.
Proof. exact (h1). Qed.
Lemma lem299797 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (h1 : term321 A a P R) : term321 A a P R.
Proof. exact (h1). Qed.
Lemma lem299798 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (h1 : term319 A a y P R) : term319 A a y P R.
Proof. exact (h1). Qed.
Lemma lem299799 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term316 A a y P R n'.
Proof. exact (h1). Qed.
Lemma lem299812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299813 {A : Type'} (f : type944 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299812 (type1597 A) (type934 A) f x). Qed.
Lemma lem299814 {A : Type'} (f : type944 A) (P : type1597 A) : (f P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P).
Proof. exact (@lem299813 A f P). Qed.
Lemma lem299815 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem299816 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R).
Proof. exact (MK_COMB (@lem299814 A f P) (@lem299815 A R)). Qed.
Lemma lem299818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299819 {A : Type'} (f : type934 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299818 (type1594 A) (type1423 A) f x). Qed.
Lemma lem299820 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R) = (term691 A f P R).
Proof. exact (@lem299819 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P) R). Qed.
Lemma lem299821 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (term691 A f P R).
Proof. exact (TRANS (@lem299816 A f P R) (@lem299820 A f P R)). Qed.
Lemma lem299822 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem299823 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term692 A f P R a).
Proof. exact (MK_COMB (@lem299821 A f P R) (@lem299822 A a)). Qed.
Lemma lem299825 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299826 {A : Type'} (f : type1423 A) (x : A) : (f x) = (@I (A -> nat -> A) f x).
Proof. exact (@lem299825 A (nat -> A) f x). Qed.
Lemma lem299827 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term692 A f P R a) = (term693 A f P R a).
Proof. exact (@lem299826 A (term691 A f P R) a). Qed.
Lemma lem299828 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term693 A f P R a).
Proof. exact (TRANS (@lem299823 A f P R a) (@lem299827 A f P R a)). Qed.
Lemma lem299829 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem299830 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (f P R a n) = (term694 A f P R a n).
Proof. exact (MK_COMB (@lem299828 A f P R a) (@lem299829 n)). Qed.
Lemma lem299832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299833 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem299832 nat A f x). Qed.
Lemma lem299834 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term694 A f P R a n) = (term695 A f P R a n).
Proof. exact (@lem299833 A (term693 A f P R a) n). Qed.
Lemma lem299836 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (f P R a n) = (term695 A f P R a n).
Proof. exact (TRANS (@lem299830 A f P R a n) (@lem299834 A f P R a n)). Qed.
Lemma lem299845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299846 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem299845 nat nat f x). Qed.
Lemma lem299848 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem299846 S n). Qed.
Lemma lem299851 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (f P R a).
Proof. exact (eq_refl (f P R a)). Qed.
Lemma lem299852 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term696 A f P R a n) = (term697 A f P R a n).
Proof. exact (MK_COMB (@lem299851 A f P R a) (@lem299848 n)). Qed.
Lemma lem299854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299855 {A : Type'} (f : type944 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299854 (type1597 A) (type934 A) f x). Qed.
Lemma lem299856 {A : Type'} (f : type944 A) (P : type1597 A) : (f P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P).
Proof. exact (@lem299855 A f P). Qed.
Lemma lem299857 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem299858 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R).
Proof. exact (MK_COMB (@lem299856 A f P) (@lem299857 A R)). Qed.
Lemma lem299860 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299861 {A : Type'} (f : type934 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299860 (type1594 A) (type1423 A) f x). Qed.
Lemma lem299862 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R) = (term691 A f P R).
Proof. exact (@lem299861 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P) R). Qed.
Lemma lem299863 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (term691 A f P R).
Proof. exact (TRANS (@lem299858 A f P R) (@lem299862 A f P R)). Qed.
Lemma lem299864 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem299865 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term692 A f P R a).
Proof. exact (MK_COMB (@lem299863 A f P R) (@lem299864 A a)). Qed.
Lemma lem299867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299868 {A : Type'} (f : type1423 A) (x : A) : (f x) = (@I (A -> nat -> A) f x).
Proof. exact (@lem299867 A (nat -> A) f x). Qed.
Lemma lem299869 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term692 A f P R a) = (term693 A f P R a).
Proof. exact (@lem299868 A (term691 A f P R) a). Qed.
Lemma lem299870 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term693 A f P R a).
Proof. exact (TRANS (@lem299865 A f P R a) (@lem299869 A f P R a)). Qed.
Lemma lem299871 (n : nat) : (@I (nat -> nat) S n) = (@I (nat -> nat) S n).
Proof. exact (eq_refl (@I (nat -> nat) S n)). Qed.
Lemma lem299872 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term697 A f P R a n) = (term698 A f P R a n).
Proof. exact (MK_COMB (@lem299870 A f P R a) (@lem299871 n)). Qed.
Lemma lem299874 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299875 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem299874 nat A f x). Qed.
Lemma lem299876 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term698 A f P R a n) = (term699 A f P R a n).
Proof. exact (@lem299875 A (term693 A f P R a) (@I (nat -> nat) S n)). Qed.
Lemma lem299877 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term697 A f P R a n) = (term699 A f P R a n).
Proof. exact (TRANS (@lem299872 A f P R a n) (@lem299876 A f P R a n)). Qed.
Lemma lem299878 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term696 A f P R a n) = (term699 A f P R a n).
Proof. exact (TRANS (@lem299852 A f P R a n) (@lem299877 A f P R a n)). Qed.
Lemma lem299879 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (R n).
Proof. exact (eq_refl (R n)). Qed.
Lemma lem299880 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term700 A f P R a n) = (term701 A f P R a n).
Proof. exact (MK_COMB (@lem299879 A R n) (@lem299836 A f P R a n)). Qed.
Lemma lem299881 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term702 A f P R a n) = (term703 A f P R a n).
Proof. exact (MK_COMB (@lem299880 A f P R a n) (@lem299878 A f P R a n)). Qed.
Lemma lem299883 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299884 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem299883 nat (type1402 A) f x). Qed.
Lemma lem299885 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem299884 A R n). Qed.
Lemma lem299886 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term695 A f P R a n) = (term695 A f P R a n).
Proof. exact (eq_refl (term695 A f P R a n)). Qed.
Lemma lem299887 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term701 A f P R a n) = (term704 A f P R a n).
Proof. exact (MK_COMB (@lem299885 A R n) (@lem299886 A f P R a n)). Qed.
Lemma lem299889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299890 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem299889 A (A -> Prop) f x). Qed.
Lemma lem299891 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term704 A f P R a n) = (term705 A f P R a n).
Proof. exact (@lem299890 A (@I (nat -> A -> A -> Prop) R n) (term695 A f P R a n)). Qed.
Lemma lem299892 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term701 A f P R a n) = (term705 A f P R a n).
Proof. exact (TRANS (@lem299887 A f P R a n) (@lem299891 A f P R a n)). Qed.
Lemma lem299893 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term699 A f P R a n) = (term699 A f P R a n).
Proof. exact (eq_refl (term699 A f P R a n)). Qed.
Lemma lem299894 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term703 A f P R a n) = (term706 A f P R a n).
Proof. exact (MK_COMB (@lem299892 A f P R a n) (@lem299893 A f P R a n)). Qed.
Lemma lem299896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299897 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem299896 A Prop f x). Qed.
Lemma lem299898 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term706 A f P R a n) = (term707 A f P R a n).
Proof. exact (@lem299897 A (term705 A f P R a n) (term699 A f P R a n)). Qed.
Lemma lem299899 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term703 A f P R a n) = (term707 A f P R a n).
Proof. exact (TRANS (@lem299894 A f P R a n) (@lem299898 A f P R a n)). Qed.
Lemma lem299900 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term702 A f P R a n) = (term707 A f P R a n).
Proof. exact (TRANS (@lem299881 A f P R a n) (@lem299899 A f P R a n)). Qed.
Lemma lem299901 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term708 A f P R a) = (term709 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem299900 A f P R a n)). Qed.
Lemma lem299902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem299903 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term710 A f P R a) = (term711 A f P R a).
Proof. exact (MK_COMB (@lem299902) (@lem299901 A f P R a)). Qed.
Lemma lem299916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299917 {A : Type'} (f : type944 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299916 (type1597 A) (type934 A) f x). Qed.
Lemma lem299918 {A : Type'} (f : type944 A) (P : type1597 A) : (f P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P).
Proof. exact (@lem299917 A f P). Qed.
Lemma lem299919 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem299920 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R).
Proof. exact (MK_COMB (@lem299918 A f P) (@lem299919 A R)). Qed.
Lemma lem299922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299923 {A : Type'} (f : type934 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299922 (type1594 A) (type1423 A) f x). Qed.
Lemma lem299924 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R) = (term691 A f P R).
Proof. exact (@lem299923 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P) R). Qed.
Lemma lem299925 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (term691 A f P R).
Proof. exact (TRANS (@lem299920 A f P R) (@lem299924 A f P R)). Qed.
Lemma lem299926 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem299927 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term692 A f P R a).
Proof. exact (MK_COMB (@lem299925 A f P R) (@lem299926 A a)). Qed.
Lemma lem299929 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299930 {A : Type'} (f : type1423 A) (x : A) : (f x) = (@I (A -> nat -> A) f x).
Proof. exact (@lem299929 A (nat -> A) f x). Qed.
Lemma lem299931 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term692 A f P R a) = (term693 A f P R a).
Proof. exact (@lem299930 A (term691 A f P R) a). Qed.
Lemma lem299932 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term693 A f P R a).
Proof. exact (TRANS (@lem299927 A f P R a) (@lem299931 A f P R a)). Qed.
Lemma lem299933 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem299934 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (f P R a n) = (term694 A f P R a n).
Proof. exact (MK_COMB (@lem299932 A f P R a) (@lem299933 n)). Qed.
Lemma lem299936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299937 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem299936 nat A f x). Qed.
Lemma lem299938 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term694 A f P R a n) = (term695 A f P R a n).
Proof. exact (@lem299937 A (term693 A f P R a) n). Qed.
Lemma lem299940 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (f P R a n) = (term695 A f P R a n).
Proof. exact (TRANS (@lem299934 A f P R a n) (@lem299938 A f P R a n)). Qed.
Lemma lem299941 {A : Type'} (P : type1597 A) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem299942 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term712 A f P R a n) = (term713 A f P R a n).
Proof. exact (MK_COMB (@lem299941 A P n) (@lem299940 A f P R a n)). Qed.
Lemma lem299944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299945 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem299944 nat (A -> Prop) f x). Qed.
Lemma lem299946 {A : Type'} (P : type1597 A) (n : nat) : (P n) = (@I (nat -> A -> Prop) P n).
Proof. exact (@lem299945 A P n). Qed.
Lemma lem299947 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term695 A f P R a n) = (term695 A f P R a n).
Proof. exact (eq_refl (term695 A f P R a n)). Qed.
Lemma lem299948 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term713 A f P R a n) = (term714 A f P R a n).
Proof. exact (MK_COMB (@lem299946 A P n) (@lem299947 A f P R a n)). Qed.
Lemma lem299950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299951 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem299950 A Prop f x). Qed.
Lemma lem299952 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term714 A f P R a n) = (term715 A f P R a n).
Proof. exact (@lem299951 A (@I (nat -> A -> Prop) P n) (term695 A f P R a n)). Qed.
Lemma lem299953 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term713 A f P R a n) = (term715 A f P R a n).
Proof. exact (TRANS (@lem299948 A f P R a n) (@lem299952 A f P R a n)). Qed.
Lemma lem299954 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term712 A f P R a n) = (term715 A f P R a n).
Proof. exact (TRANS (@lem299942 A f P R a n) (@lem299953 A f P R a n)). Qed.
Lemma lem299955 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term716 A f P R a) = (term717 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem299954 A f P R a n)). Qed.
Lemma lem299956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem299957 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term718 A f P R a) = (term719 A f P R a).
Proof. exact (MK_COMB (@lem299956) (@lem299955 A f P R a)). Qed.
Lemma lem299958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem299959 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term720 A f P R a) = (term721 A f P R a).
Proof. exact (MK_COMB (@lem299958) (@lem299957 A f P R a)). Qed.
Lemma lem299960 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term722 A f P R a) = (term723 A f P R a).
Proof. exact (MK_COMB (@lem299959 A f P R a) (@lem299903 A f P R a)). Qed.
Lemma lem299961 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem299970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299971 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem299970 nat nat f x). Qed.
Lemma lem299973 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem299971 NUMERAL 0). Qed.
Lemma lem299976 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (f P R a).
Proof. exact (eq_refl (f P R a)). Qed.
Lemma lem299977 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term724 A f P R a) = (term725 A f P R a).
Proof. exact (MK_COMB (@lem299976 A f P R a) (@lem299973)). Qed.
Lemma lem299979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299980 {A : Type'} (f : type944 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299979 (type1597 A) (type934 A) f x). Qed.
Lemma lem299981 {A : Type'} (f : type944 A) (P : type1597 A) : (f P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P).
Proof. exact (@lem299980 A f P). Qed.
Lemma lem299982 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem299983 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R).
Proof. exact (MK_COMB (@lem299981 A f P) (@lem299982 A R)). Qed.
Lemma lem299985 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299986 {A : Type'} (f : type934 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat -> A) f x).
Proof. exact (@lem299985 (type1594 A) (type1423 A) f x). Qed.
Lemma lem299987 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P R) = (term691 A f P R).
Proof. exact (@lem299986 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat -> A) f P) R). Qed.
Lemma lem299988 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) : (f P R) = (term691 A f P R).
Proof. exact (TRANS (@lem299983 A f P R) (@lem299987 A f P R)). Qed.
Lemma lem299989 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem299990 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term692 A f P R a).
Proof. exact (MK_COMB (@lem299988 A f P R) (@lem299989 A a)). Qed.
Lemma lem299992 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem299993 {A : Type'} (f : type1423 A) (x : A) : (f x) = (@I (A -> nat -> A) f x).
Proof. exact (@lem299992 A (nat -> A) f x). Qed.
Lemma lem299994 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term692 A f P R a) = (term693 A f P R a).
Proof. exact (@lem299993 A (term691 A f P R) a). Qed.
Lemma lem299995 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (f P R a) = (term693 A f P R a).
Proof. exact (TRANS (@lem299990 A f P R a) (@lem299994 A f P R a)). Qed.
Lemma lem299996 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem299997 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term725 A f P R a) = (term726 A f P R a).
Proof. exact (MK_COMB (@lem299995 A f P R a) (@lem299996)). Qed.
Lemma lem299999 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300000 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem299999 nat A f x). Qed.
Lemma lem300001 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term726 A f P R a) = (term727 A f P R a).
Proof. exact (@lem300000 A (term693 A f P R a) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem300002 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term725 A f P R a) = (term727 A f P R a).
Proof. exact (TRANS (@lem299997 A f P R a) (@lem300001 A f P R a)). Qed.
Lemma lem300003 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term724 A f P R a) = (term727 A f P R a).
Proof. exact (TRANS (@lem299977 A f P R a) (@lem300002 A f P R a)). Qed.
Lemma lem300004 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300005 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term728 A f P R a) = (term729 A f P R a).
Proof. exact (MK_COMB (@lem299961 A) (@lem300003 A f P R a)). Qed.
Lemma lem300006 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term724 A f P R a) = a) = ((term727 A f P R a) = a).
Proof. exact (MK_COMB (@lem300005 A f P R a) (@lem300004 A a)). Qed.
Lemma lem300007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300008 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term730 A f P R a) = (term731 A f P R a).
Proof. exact (MK_COMB (@lem300007) (@lem300006 A f P R a)). Qed.
Lemma lem300009 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term732 A f P R a) = (term733 A f P R a).
Proof. exact (MK_COMB (@lem300008 A f P R a) (@lem299960 A f P R a)). Qed.
Lemma lem300010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem300011 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300021 {A : Type'} (f : type946 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) f x).
Proof. exact (@lem300020 (type1597 A) (type936 A) f x). Qed.
Lemma lem300022 {A : Type'} (n : type946 A) (P : type1597 A) : (n P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P).
Proof. exact (@lem300021 A n P). Qed.
Lemma lem300023 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300024 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (n P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P R).
Proof. exact (MK_COMB (@lem300022 A n P) (@lem300023 A R)). Qed.
Lemma lem300026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300027 {A : Type'} (f : type936 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat) f x).
Proof. exact (@lem300026 (type1594 A) (A -> nat) f x). Qed.
Lemma lem300028 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P R) = (term734 A n P R).
Proof. exact (@lem300027 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P) R). Qed.
Lemma lem300029 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (n P R) = (term734 A n P R).
Proof. exact (TRANS (@lem300024 A n P R) (@lem300028 A n P R)). Qed.
Lemma lem300030 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300031 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (n P R a) = (term735 A n P R a).
Proof. exact (MK_COMB (@lem300029 A n P R) (@lem300030 A a)). Qed.
Lemma lem300033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300034 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem300033 A nat f x). Qed.
Lemma lem300035 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term735 A n P R a) = (term736 A n P R a).
Proof. exact (@lem300034 A (term734 A n P R) a). Qed.
Lemma lem300037 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (n P R a) = (term736 A n P R a).
Proof. exact (TRANS (@lem300031 A n P R a) (@lem300035 A n P R a)). Qed.
Lemma lem300046 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300047 {A : Type'} (f : type945 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) f x).
Proof. exact (@lem300046 (type1597 A) (type935 A) f x). Qed.
Lemma lem300048 {A : Type'} (x : type945 A) (P : type1597 A) : (x P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P).
Proof. exact (@lem300047 A x P). Qed.
Lemma lem300049 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300050 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) : (x P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P R).
Proof. exact (MK_COMB (@lem300048 A x P) (@lem300049 A R)). Qed.
Lemma lem300052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300053 {A : Type'} (f : type935 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> A) f x).
Proof. exact (@lem300052 (type1594 A) (A -> A) f x). Qed.
Lemma lem300054 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P R) = (term737 A x P R).
Proof. exact (@lem300053 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P) R). Qed.
Lemma lem300055 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) : (x P R) = (term737 A x P R).
Proof. exact (TRANS (@lem300050 A x P R) (@lem300054 A x P R)). Qed.
Lemma lem300056 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300057 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (x P R a) = (term738 A x P R a).
Proof. exact (MK_COMB (@lem300055 A x P R) (@lem300056 A a)). Qed.
Lemma lem300059 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300060 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem300059 A A f x). Qed.
Lemma lem300061 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term738 A x P R a) = (term739 A x P R a).
Proof. exact (@lem300060 A (term737 A x P R) a). Qed.
Lemma lem300063 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (x P R a) = (term739 A x P R a).
Proof. exact (TRANS (@lem300057 A x P R a) (@lem300061 A x P R a)). Qed.
Lemma lem300064 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem300065 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term740 A n P R a) = (term741 A n P R a).
Proof. exact (MK_COMB (@lem300011 A R) (@lem300037 A n P R a)). Qed.
Lemma lem300066 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term742 A n x P R a) = (term743 A n x P R a).
Proof. exact (MK_COMB (@lem300065 A n P R a) (@lem300063 A x P R a)). Qed.
Lemma lem300067 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term744 A n x P R a y) = (term745 A n x P R a y).
Proof. exact (MK_COMB (@lem300066 A n x P R a) (@lem300064 A y)). Qed.
Lemma lem300069 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300070 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem300069 nat (type1402 A) f x). Qed.
Lemma lem300071 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term741 A n P R a) = (term746 A n P R a).
Proof. exact (@lem300070 A R (term736 A n P R a)). Qed.
Lemma lem300072 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term739 A x P R a) = (term739 A x P R a).
Proof. exact (eq_refl (term739 A x P R a)). Qed.
Lemma lem300073 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term743 A n x P R a) = (term747 A n x P R a).
Proof. exact (MK_COMB (@lem300071 A n P R a) (@lem300072 A x P R a)). Qed.
Lemma lem300075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300076 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem300075 A (A -> Prop) f x). Qed.
Lemma lem300077 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term747 A n x P R a) = (term748 A n x P R a).
Proof. exact (@lem300076 A (term746 A n P R a) (term739 A x P R a)). Qed.
Lemma lem300078 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term743 A n x P R a) = (term748 A n x P R a).
Proof. exact (TRANS (@lem300073 A n x P R a) (@lem300077 A n x P R a)). Qed.
Lemma lem300079 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem300080 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term745 A n x P R a y) = (term749 A n x P R a y).
Proof. exact (MK_COMB (@lem300078 A n x P R a) (@lem300079 A y)). Qed.
Lemma lem300082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300083 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300082 A Prop f x). Qed.
Lemma lem300084 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term749 A n x P R a y) = (term750 A n x P R a y).
Proof. exact (@lem300083 A (term748 A n x P R a) y). Qed.
Lemma lem300085 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term745 A n x P R a y) = (term750 A n x P R a y).
Proof. exact (TRANS (@lem300080 A n x P R a y) (@lem300084 A n x P R a y)). Qed.
Lemma lem300086 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term744 A n x P R a y) = (term750 A n x P R a y).
Proof. exact (TRANS (@lem300067 A n x P R a y) (@lem300085 A n x P R a y)). Qed.
Lemma lem300087 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term751 A n x P R a y) = (term752 A n x P R a y).
Proof. exact (MK_COMB (@lem300010) (@lem300086 A n x P R a y)). Qed.
Lemma lem300088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem300089 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem300090 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem300099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300100 {A : Type'} (f : type946 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) f x).
Proof. exact (@lem300099 (type1597 A) (type936 A) f x). Qed.
Lemma lem300101 {A : Type'} (n : type946 A) (P : type1597 A) : (n P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P).
Proof. exact (@lem300100 A n P). Qed.
Lemma lem300102 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300103 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (n P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P R).
Proof. exact (MK_COMB (@lem300101 A n P) (@lem300102 A R)). Qed.
Lemma lem300105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300106 {A : Type'} (f : type936 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat) f x).
Proof. exact (@lem300105 (type1594 A) (A -> nat) f x). Qed.
Lemma lem300107 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P R) = (term734 A n P R).
Proof. exact (@lem300106 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P) R). Qed.
Lemma lem300108 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (n P R) = (term734 A n P R).
Proof. exact (TRANS (@lem300103 A n P R) (@lem300107 A n P R)). Qed.
Lemma lem300109 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300110 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (n P R a) = (term735 A n P R a).
Proof. exact (MK_COMB (@lem300108 A n P R) (@lem300109 A a)). Qed.
Lemma lem300112 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300113 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem300112 A nat f x). Qed.
Lemma lem300114 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term735 A n P R a) = (term736 A n P R a).
Proof. exact (@lem300113 A (term734 A n P R) a). Qed.
Lemma lem300116 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (n P R a) = (term736 A n P R a).
Proof. exact (TRANS (@lem300110 A n P R a) (@lem300114 A n P R a)). Qed.
Lemma lem300117 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term753 A n P R a) = (term754 A n P R a).
Proof. exact (MK_COMB (@lem300090) (@lem300116 A n P R a)). Qed.
Lemma lem300119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300120 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem300119 nat nat f x). Qed.
Lemma lem300121 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term754 A n P R a) = (term755 A n P R a).
Proof. exact (@lem300120 S (term736 A n P R a)). Qed.
Lemma lem300122 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term753 A n P R a) = (term755 A n P R a).
Proof. exact (TRANS (@lem300117 A n P R a) (@lem300121 A n P R a)). Qed.
Lemma lem300123 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem300124 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term756 A n P R a) = (term757 A n P R a).
Proof. exact (MK_COMB (@lem300089 A P) (@lem300122 A n P R a)). Qed.
Lemma lem300125 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term758 A n P R a y) = (term759 A n P R a y).
Proof. exact (MK_COMB (@lem300124 A n P R a) (@lem300123 A y)). Qed.
Lemma lem300127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300128 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300127 nat (A -> Prop) f x). Qed.
Lemma lem300129 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term757 A n P R a) = (term760 A n P R a).
Proof. exact (@lem300128 A P (term755 A n P R a)). Qed.
Lemma lem300130 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem300131 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term759 A n P R a y) = (term761 A n P R a y).
Proof. exact (MK_COMB (@lem300129 A n P R a) (@lem300130 A y)). Qed.
Lemma lem300133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300134 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300133 A Prop f x). Qed.
Lemma lem300135 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term761 A n P R a y) = (term762 A n P R a y).
Proof. exact (@lem300134 A (term760 A n P R a) y). Qed.
Lemma lem300136 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term759 A n P R a y) = (term762 A n P R a y).
Proof. exact (TRANS (@lem300131 A n P R a y) (@lem300135 A n P R a y)). Qed.
Lemma lem300137 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term758 A n P R a y) = (term762 A n P R a y).
Proof. exact (TRANS (@lem300125 A n P R a y) (@lem300136 A n P R a y)). Qed.
Lemma lem300138 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term763 A n P R a y) = (term764 A n P R a y).
Proof. exact (MK_COMB (@lem300088) (@lem300137 A n P R a y)). Qed.
Lemma lem300139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300140 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term765 A n P R a y) = (term766 A n P R a y).
Proof. exact (MK_COMB (@lem300139) (@lem300138 A n P R a y)). Qed.
Lemma lem300141 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term767 A n x P R a y) = (term768 A n x P R a y).
Proof. exact (MK_COMB (@lem300140 A n P R a y) (@lem300087 A n x P R a y)). Qed.
Lemma lem300142 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term769 A n x P R a) = (term770 A n x P R a).
Proof. exact (fun_ext (fun y : A => @lem300141 A n x P R a y)). Qed.
Lemma lem300143 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300144 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term771 A n x P R a) = (term772 A n x P R a).
Proof. exact (MK_COMB (@lem300143 A) (@lem300142 A n x P R a)). Qed.
Lemma lem300145 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem300154 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300155 {A : Type'} (f : type946 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) f x).
Proof. exact (@lem300154 (type1597 A) (type936 A) f x). Qed.
Lemma lem300156 {A : Type'} (n : type946 A) (P : type1597 A) : (n P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P).
Proof. exact (@lem300155 A n P). Qed.
Lemma lem300157 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300158 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (n P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P R).
Proof. exact (MK_COMB (@lem300156 A n P) (@lem300157 A R)). Qed.
Lemma lem300160 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300161 {A : Type'} (f : type936 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> nat) f x).
Proof. exact (@lem300160 (type1594 A) (A -> nat) f x). Qed.
Lemma lem300162 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P R) = (term734 A n P R).
Proof. exact (@lem300161 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> nat) n P) R). Qed.
Lemma lem300163 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) : (n P R) = (term734 A n P R).
Proof. exact (TRANS (@lem300158 A n P R) (@lem300162 A n P R)). Qed.
Lemma lem300164 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300165 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (n P R a) = (term735 A n P R a).
Proof. exact (MK_COMB (@lem300163 A n P R) (@lem300164 A a)). Qed.
Lemma lem300167 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300168 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem300167 A nat f x). Qed.
Lemma lem300169 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term735 A n P R a) = (term736 A n P R a).
Proof. exact (@lem300168 A (term734 A n P R) a). Qed.
Lemma lem300171 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (n P R a) = (term736 A n P R a).
Proof. exact (TRANS (@lem300165 A n P R a) (@lem300169 A n P R a)). Qed.
Lemma lem300180 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300181 {A : Type'} (f : type945 A) (x : type1597 A) : (f x) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) f x).
Proof. exact (@lem300180 (type1597 A) (type935 A) f x). Qed.
Lemma lem300182 {A : Type'} (x : type945 A) (P : type1597 A) : (x P) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P).
Proof. exact (@lem300181 A x P). Qed.
Lemma lem300183 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300184 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) : (x P R) = (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P R).
Proof. exact (MK_COMB (@lem300182 A x P) (@lem300183 A R)). Qed.
Lemma lem300186 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300187 {A : Type'} (f : type935 A) (x : type1594 A) : (f x) = (@I ((nat -> A -> A -> Prop) -> A -> A) f x).
Proof. exact (@lem300186 (type1594 A) (A -> A) f x). Qed.
Lemma lem300188 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) : (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P R) = (term737 A x P R).
Proof. exact (@lem300187 A (@I ((nat -> A -> Prop) -> (nat -> A -> A -> Prop) -> A -> A) x P) R). Qed.
Lemma lem300189 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) : (x P R) = (term737 A x P R).
Proof. exact (TRANS (@lem300184 A x P R) (@lem300188 A x P R)). Qed.
Lemma lem300190 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300191 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (x P R a) = (term738 A x P R a).
Proof. exact (MK_COMB (@lem300189 A x P R) (@lem300190 A a)). Qed.
Lemma lem300193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300194 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem300193 A A f x). Qed.
Lemma lem300195 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term738 A x P R a) = (term739 A x P R a).
Proof. exact (@lem300194 A (term737 A x P R) a). Qed.
Lemma lem300197 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (x P R a) = (term739 A x P R a).
Proof. exact (TRANS (@lem300191 A x P R a) (@lem300195 A x P R a)). Qed.
Lemma lem300198 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term773 A n P R a) = (term774 A n P R a).
Proof. exact (MK_COMB (@lem300145 A P) (@lem300171 A n P R a)). Qed.
Lemma lem300199 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term775 A n x P R a) = (term776 A n x P R a).
Proof. exact (MK_COMB (@lem300198 A n P R a) (@lem300197 A x P R a)). Qed.
Lemma lem300201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300202 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300201 nat (A -> Prop) f x). Qed.
Lemma lem300203 {A : Type'} (n : type946 A) (P : type1597 A) (R : type1594 A) (a : A) : (term774 A n P R a) = (term777 A n P R a).
Proof. exact (@lem300202 A P (term736 A n P R a)). Qed.
Lemma lem300204 {A : Type'} (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term739 A x P R a) = (term739 A x P R a).
Proof. exact (eq_refl (term739 A x P R a)). Qed.
Lemma lem300205 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term776 A n x P R a) = (term778 A n x P R a).
Proof. exact (MK_COMB (@lem300203 A n P R a) (@lem300204 A x P R a)). Qed.
Lemma lem300207 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300208 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300207 A Prop f x). Qed.
Lemma lem300209 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term778 A n x P R a) = (term779 A n x P R a).
Proof. exact (@lem300208 A (term777 A n P R a) (term739 A x P R a)). Qed.
Lemma lem300210 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term776 A n x P R a) = (term779 A n x P R a).
Proof. exact (TRANS (@lem300205 A n x P R a) (@lem300209 A n x P R a)). Qed.
Lemma lem300211 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term775 A n x P R a) = (term779 A n x P R a).
Proof. exact (TRANS (@lem300199 A n x P R a) (@lem300210 A n x P R a)). Qed.
Lemma lem300212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300213 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term780 A n x P R a) = (term781 A n x P R a).
Proof. exact (MK_COMB (@lem300212) (@lem300211 A n x P R a)). Qed.
Lemma lem300214 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term782 A n x P R a) = (term783 A n x P R a).
Proof. exact (MK_COMB (@lem300213 A n x P R a) (@lem300144 A n x P R a)). Qed.
Lemma lem300215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem300216 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem300221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300222 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem300221 nat nat f x). Qed.
Lemma lem300224 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem300222 NUMERAL 0). Qed.
Lemma lem300225 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300226 {A : Type'} (P : type1597 A) : (term784 A P) = (term785 A P).
Proof. exact (MK_COMB (@lem300216 A P) (@lem300224)). Qed.
Lemma lem300227 {A : Type'} (P : type1597 A) (a : A) : (term52 A P a) = (term786 A P a).
Proof. exact (MK_COMB (@lem300226 A P) (@lem300225 A a)). Qed.
Lemma lem300229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300230 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300229 nat (A -> Prop) f x). Qed.
Lemma lem300231 {A : Type'} (P : type1597 A) : (term785 A P) = (term787 A P).
Proof. exact (@lem300230 A P (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem300232 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300233 {A : Type'} (P : type1597 A) (a : A) : (term786 A P a) = (term788 A P a).
Proof. exact (MK_COMB (@lem300231 A P) (@lem300232 A a)). Qed.
Lemma lem300235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300236 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300235 A Prop f x). Qed.
Lemma lem300237 {A : Type'} (P : type1597 A) (a : A) : (term788 A P a) = (term789 A P a).
Proof. exact (@lem300236 A (term787 A P) a). Qed.
Lemma lem300238 {A : Type'} (P : type1597 A) (a : A) : (term786 A P a) = (term789 A P a).
Proof. exact (TRANS (@lem300233 A P a) (@lem300237 A P a)). Qed.
Lemma lem300239 {A : Type'} (P : type1597 A) (a : A) : (term52 A P a) = (term789 A P a).
Proof. exact (TRANS (@lem300227 A P a) (@lem300238 A P a)). Qed.
Lemma lem300240 {A : Type'} (P : type1597 A) (a : A) : (term377 A P a) = (term790 A P a).
Proof. exact (MK_COMB (@lem300215) (@lem300239 A P a)). Qed.
Lemma lem300241 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300242 {A : Type'} (P : type1597 A) (a : A) : (term359 A P a) = (term791 A P a).
Proof. exact (MK_COMB (@lem300241) (@lem300240 A P a)). Qed.
Lemma lem300243 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term792 A n x P R a) = (term793 A n x P R a).
Proof. exact (MK_COMB (@lem300242 A P a) (@lem300214 A n x P R a)). Qed.
Lemma lem300244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300245 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term794 A n x P R a) = (term795 A n x P R a).
Proof. exact (MK_COMB (@lem300244) (@lem300243 A n x P R a)). Qed.
Lemma lem300246 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term796 A n x f P R a) = (term797 A n x f P R a).
Proof. exact (MK_COMB (@lem300245 A n x P R a) (@lem300009 A f P R a)). Qed.
Lemma lem300247 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) : (term798 A n x f P R) = (term799 A n x f P R).
Proof. exact (fun_ext (fun a : A => @lem300246 A n x f P R a)). Qed.
Lemma lem300248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300249 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) : (term800 A n x f P R) = (term801 A n x f P R).
Proof. exact (MK_COMB (@lem300248 A) (@lem300247 A n x f P R)). Qed.
Lemma lem300250 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term802 A n x f P) = (term803 A n x f P).
Proof. exact (fun_ext (fun R : type1594 A => @lem300249 A n x f P R)). Qed.
Lemma lem300251 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem300252 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term679 A n x f P) = (term804 A n x f P).
Proof. exact (MK_COMB (@lem300251 A) (@lem300250 A n x f P)). Qed.
Lemma lem300253 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term681 A n x f) = (term805 A n x f).
Proof. exact (fun_ext (fun P : type1597 A => @lem300252 A n x f P)). Qed.
Lemma lem300254 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem300255 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term683 A n x f) = (term806 A n x f).
Proof. exact (MK_COMB (@lem300254 A) (@lem300253 A n x f)). Qed.
Lemma lem300256 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term806 A n x f.
Proof. exact (EQ_MP (@lem300255 A n x f) (@lem299794 A n x f h1)). Qed.
Lemma lem300257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem300258 {A : Type'} (R : type1594 A) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem300263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300264 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem300263 (nat -> A) nat f x). Qed.
Lemma lem300266 {A : Type'} (n' : type977 A) (f : nat -> A) : (n' f) = (@I ((nat -> A) -> nat) n' f).
Proof. exact (@lem300264 A n' f). Qed.
Lemma lem300267 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem300272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300273 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem300272 (nat -> A) nat f x). Qed.
Lemma lem300275 {A : Type'} (n' : type977 A) (f : nat -> A) : (n' f) = (@I ((nat -> A) -> nat) n' f).
Proof. exact (@lem300273 A n' f). Qed.
Lemma lem300276 {A : Type'} (n' : type977 A) (f : nat -> A) : (term807 A n' f) = (term808 A n' f).
Proof. exact (MK_COMB (@lem300267 A f) (@lem300275 A n' f)). Qed.
Lemma lem300278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300279 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem300278 nat A f x). Qed.
Lemma lem300280 {A : Type'} (n' : type977 A) (f : nat -> A) : (term808 A n' f) = (term809 A n' f).
Proof. exact (@lem300279 A f (@I ((nat -> A) -> nat) n' f)). Qed.
Lemma lem300281 {A : Type'} (n' : type977 A) (f : nat -> A) : (term807 A n' f) = (term809 A n' f).
Proof. exact (TRANS (@lem300276 A n' f) (@lem300280 A n' f)). Qed.
Lemma lem300282 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem300283 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem300288 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300289 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem300288 (nat -> A) nat f x). Qed.
Lemma lem300291 {A : Type'} (n' : type977 A) (f : nat -> A) : (n' f) = (@I ((nat -> A) -> nat) n' f).
Proof. exact (@lem300289 A n' f). Qed.
Lemma lem300292 {A : Type'} (n' : type977 A) (f : nat -> A) : (term810 A n' f) = (term811 A n' f).
Proof. exact (MK_COMB (@lem300283) (@lem300291 A n' f)). Qed.
Lemma lem300294 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300295 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem300294 nat nat f x). Qed.
Lemma lem300296 {A : Type'} (n' : type977 A) (f : nat -> A) : (term811 A n' f) = (term812 A n' f).
Proof. exact (@lem300295 S (@I ((nat -> A) -> nat) n' f)). Qed.
Lemma lem300297 {A : Type'} (n' : type977 A) (f : nat -> A) : (term810 A n' f) = (term812 A n' f).
Proof. exact (TRANS (@lem300292 A n' f) (@lem300296 A n' f)). Qed.
Lemma lem300298 {A : Type'} (n' : type977 A) (f : nat -> A) : (term813 A n' f) = (term814 A n' f).
Proof. exact (MK_COMB (@lem300282 A f) (@lem300297 A n' f)). Qed.
Lemma lem300300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300301 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem300300 nat A f x). Qed.
Lemma lem300302 {A : Type'} (n' : type977 A) (f : nat -> A) : (term814 A n' f) = (term815 A n' f).
Proof. exact (@lem300301 A f (term812 A n' f)). Qed.
Lemma lem300303 {A : Type'} (n' : type977 A) (f : nat -> A) : (term813 A n' f) = (term815 A n' f).
Proof. exact (TRANS (@lem300298 A n' f) (@lem300302 A n' f)). Qed.
Lemma lem300304 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term816 A R n' f) = (term817 A R n' f).
Proof. exact (MK_COMB (@lem300258 A R) (@lem300266 A n' f)). Qed.
Lemma lem300305 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term818 A R n' f) = (term819 A R n' f).
Proof. exact (MK_COMB (@lem300304 A R n' f) (@lem300281 A n' f)). Qed.
Lemma lem300306 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term820 A R n' f) = (term821 A R n' f).
Proof. exact (MK_COMB (@lem300305 A R n' f) (@lem300303 A n' f)). Qed.
Lemma lem300308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300309 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem300308 nat (type1402 A) f x). Qed.
Lemma lem300310 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term817 A R n' f) = (term822 A R n' f).
Proof. exact (@lem300309 A R (@I ((nat -> A) -> nat) n' f)). Qed.
Lemma lem300311 {A : Type'} (n' : type977 A) (f : nat -> A) : (term809 A n' f) = (term809 A n' f).
Proof. exact (eq_refl (term809 A n' f)). Qed.
Lemma lem300312 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term819 A R n' f) = (term823 A R n' f).
Proof. exact (MK_COMB (@lem300310 A R n' f) (@lem300311 A n' f)). Qed.
Lemma lem300314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300315 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem300314 A (A -> Prop) f x). Qed.
Lemma lem300316 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term823 A R n' f) = (term824 A R n' f).
Proof. exact (@lem300315 A (term822 A R n' f) (term809 A n' f)). Qed.
Lemma lem300317 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term819 A R n' f) = (term824 A R n' f).
Proof. exact (TRANS (@lem300312 A R n' f) (@lem300316 A R n' f)). Qed.
Lemma lem300318 {A : Type'} (n' : type977 A) (f : nat -> A) : (term815 A n' f) = (term815 A n' f).
Proof. exact (eq_refl (term815 A n' f)). Qed.
Lemma lem300319 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term821 A R n' f) = (term825 A R n' f).
Proof. exact (MK_COMB (@lem300317 A R n' f) (@lem300318 A n' f)). Qed.
Lemma lem300321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300322 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300321 A Prop f x). Qed.
Lemma lem300323 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term825 A R n' f) = (term826 A R n' f).
Proof. exact (@lem300322 A (term824 A R n' f) (term815 A n' f)). Qed.
Lemma lem300324 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term821 A R n' f) = (term826 A R n' f).
Proof. exact (TRANS (@lem300319 A R n' f) (@lem300323 A R n' f)). Qed.
Lemma lem300325 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term820 A R n' f) = (term826 A R n' f).
Proof. exact (TRANS (@lem300306 A R n' f) (@lem300324 A R n' f)). Qed.
Lemma lem300326 {A : Type'} (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term827 A R n' f) = (term828 A R n' f).
Proof. exact (MK_COMB (@lem300257) (@lem300325 A R n' f)). Qed.
Lemma lem300327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem300328 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem300333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300334 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem300333 (nat -> A) nat f x). Qed.
Lemma lem300336 {A : Type'} (n' : type977 A) (f : nat -> A) : (n' f) = (@I ((nat -> A) -> nat) n' f).
Proof. exact (@lem300334 A n' f). Qed.
Lemma lem300337 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem300342 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300343 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem300342 (nat -> A) nat f x). Qed.
Lemma lem300345 {A : Type'} (n' : type977 A) (f : nat -> A) : (n' f) = (@I ((nat -> A) -> nat) n' f).
Proof. exact (@lem300343 A n' f). Qed.
Lemma lem300346 {A : Type'} (n' : type977 A) (f : nat -> A) : (term807 A n' f) = (term808 A n' f).
Proof. exact (MK_COMB (@lem300337 A f) (@lem300345 A n' f)). Qed.
Lemma lem300348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300349 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem300348 nat A f x). Qed.
Lemma lem300350 {A : Type'} (n' : type977 A) (f : nat -> A) : (term808 A n' f) = (term809 A n' f).
Proof. exact (@lem300349 A f (@I ((nat -> A) -> nat) n' f)). Qed.
Lemma lem300351 {A : Type'} (n' : type977 A) (f : nat -> A) : (term807 A n' f) = (term809 A n' f).
Proof. exact (TRANS (@lem300346 A n' f) (@lem300350 A n' f)). Qed.
Lemma lem300352 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term829 A P n' f) = (term830 A P n' f).
Proof. exact (MK_COMB (@lem300328 A P) (@lem300336 A n' f)). Qed.
Lemma lem300353 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term831 A P n' f) = (term832 A P n' f).
Proof. exact (MK_COMB (@lem300352 A P n' f) (@lem300351 A n' f)). Qed.
Lemma lem300355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300356 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300355 nat (A -> Prop) f x). Qed.
Lemma lem300357 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term830 A P n' f) = (term833 A P n' f).
Proof. exact (@lem300356 A P (@I ((nat -> A) -> nat) n' f)). Qed.
Lemma lem300358 {A : Type'} (n' : type977 A) (f : nat -> A) : (term809 A n' f) = (term809 A n' f).
Proof. exact (eq_refl (term809 A n' f)). Qed.
Lemma lem300359 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term832 A P n' f) = (term834 A P n' f).
Proof. exact (MK_COMB (@lem300357 A P n' f) (@lem300358 A n' f)). Qed.
Lemma lem300361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300362 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300361 A Prop f x). Qed.
Lemma lem300363 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term834 A P n' f) = (term835 A P n' f).
Proof. exact (@lem300362 A (term833 A P n' f) (term809 A n' f)). Qed.
Lemma lem300364 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term832 A P n' f) = (term835 A P n' f).
Proof. exact (TRANS (@lem300359 A P n' f) (@lem300363 A P n' f)). Qed.
Lemma lem300365 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term831 A P n' f) = (term835 A P n' f).
Proof. exact (TRANS (@lem300353 A P n' f) (@lem300364 A P n' f)). Qed.
Lemma lem300366 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term836 A P n' f) = (term837 A P n' f).
Proof. exact (MK_COMB (@lem300327) (@lem300365 A P n' f)). Qed.
Lemma lem300367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300368 {A : Type'} (P : type1597 A) (n' : type977 A) (f : nat -> A) : (term838 A P n' f) = (term839 A P n' f).
Proof. exact (MK_COMB (@lem300367) (@lem300366 A P n' f)). Qed.
Lemma lem300369 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term265 A P R n' f) = (term840 A P R n' f).
Proof. exact (MK_COMB (@lem300368 A P n' f) (@lem300326 A R n' f)). Qed.
Lemma lem300370 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) : (term267 A P R n') = (term841 A P R n').
Proof. exact (fun_ext (fun f : nat -> A => @lem300369 A P R n' f)). Qed.
Lemma lem300371 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem300372 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) : (term269 A P R n') = (term842 A P R n').
Proof. exact (MK_COMB (@lem300371 A) (@lem300370 A P R n')). Qed.
Lemma lem300382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300383 {A : Type'} (f : type1596 A) (x : nat) : (f x) = (@I (nat -> A -> A) f x).
Proof. exact (@lem300382 nat (A -> A) f x). Qed.
Lemma lem300384 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (@I (nat -> A -> A) y n).
Proof. exact (@lem300383 A y n). Qed.
Lemma lem300385 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem300386 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (@I (nat -> A -> A) y n x).
Proof. exact (MK_COMB (@lem300384 A y n) (@lem300385 A x)). Qed.
Lemma lem300388 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300389 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem300388 A A f x). Qed.
Lemma lem300390 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (@I (nat -> A -> A) y n x) = (term843 A y n x).
Proof. exact (@lem300389 A (@I (nat -> A -> A) y n) x). Qed.
Lemma lem300392 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (term843 A y n x).
Proof. exact (TRANS (@lem300386 A y n x) (@lem300390 A y n x)). Qed.
Lemma lem300394 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (R n x).
Proof. exact (eq_refl (R n x)). Qed.
Lemma lem300395 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term844 A R y n x) = (term845 A R y n x).
Proof. exact (MK_COMB (@lem300394 A R n x) (@lem300392 A y n x)). Qed.
Lemma lem300397 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300398 {A : Type'} (f : type1594 A) (x : nat) : (f x) = (@I (nat -> A -> A -> Prop) f x).
Proof. exact (@lem300397 nat (type1402 A) f x). Qed.
Lemma lem300399 {A : Type'} (R : type1594 A) (n : nat) : (R n) = (@I (nat -> A -> A -> Prop) R n).
Proof. exact (@lem300398 A R n). Qed.
Lemma lem300400 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem300401 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (@I (nat -> A -> A -> Prop) R n x).
Proof. exact (MK_COMB (@lem300399 A R n) (@lem300400 A x)). Qed.
Lemma lem300403 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300404 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem300403 A (A -> Prop) f x). Qed.
Lemma lem300405 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (@I (nat -> A -> A -> Prop) R n x) = (term846 A R n x).
Proof. exact (@lem300404 A (@I (nat -> A -> A -> Prop) R n) x). Qed.
Lemma lem300406 {A : Type'} (R : type1594 A) (n : nat) (x : A) : (R n x) = (term846 A R n x).
Proof. exact (TRANS (@lem300401 A R n x) (@lem300405 A R n x)). Qed.
Lemma lem300407 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (term843 A y n x) = (term843 A y n x).
Proof. exact (eq_refl (term843 A y n x)). Qed.
Lemma lem300408 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term845 A R y n x) = (term847 A R y n x).
Proof. exact (MK_COMB (@lem300406 A R n x) (@lem300407 A y n x)). Qed.
Lemma lem300410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300411 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300410 A Prop f x). Qed.
Lemma lem300412 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term847 A R y n x) = (term848 A R y n x).
Proof. exact (@lem300411 A (term846 A R n x) (term843 A y n x)). Qed.
Lemma lem300413 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term845 A R y n x) = (term848 A R y n x).
Proof. exact (TRANS (@lem300408 A R y n x) (@lem300412 A R y n x)). Qed.
Lemma lem300414 {A : Type'} (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term844 A R y n x) = (term848 A R y n x).
Proof. exact (TRANS (@lem300395 A R y n x) (@lem300413 A R y n x)). Qed.
Lemma lem300415 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem300420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300421 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem300420 nat nat f x). Qed.
Lemma lem300423 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem300421 S n). Qed.
Lemma lem300430 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300431 {A : Type'} (f : type1596 A) (x : nat) : (f x) = (@I (nat -> A -> A) f x).
Proof. exact (@lem300430 nat (A -> A) f x). Qed.
Lemma lem300432 {A : Type'} (y : type1596 A) (n : nat) : (y n) = (@I (nat -> A -> A) y n).
Proof. exact (@lem300431 A y n). Qed.
Lemma lem300433 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem300434 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (@I (nat -> A -> A) y n x).
Proof. exact (MK_COMB (@lem300432 A y n) (@lem300433 A x)). Qed.
Lemma lem300436 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300437 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem300436 A A f x). Qed.
Lemma lem300438 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (@I (nat -> A -> A) y n x) = (term843 A y n x).
Proof. exact (@lem300437 A (@I (nat -> A -> A) y n) x). Qed.
Lemma lem300440 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (y n x) = (term843 A y n x).
Proof. exact (TRANS (@lem300434 A y n x) (@lem300438 A y n x)). Qed.
Lemma lem300441 {A : Type'} (P : type1597 A) (n : nat) : (term849 A P n) = (term850 A P n).
Proof. exact (MK_COMB (@lem300415 A P) (@lem300423 n)). Qed.
Lemma lem300442 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term851 A P y n x) = (term852 A P y n x).
Proof. exact (MK_COMB (@lem300441 A P n) (@lem300440 A y n x)). Qed.
Lemma lem300444 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300445 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300444 nat (A -> Prop) f x). Qed.
Lemma lem300446 {A : Type'} (P : type1597 A) (n : nat) : (term850 A P n) = (term853 A P n).
Proof. exact (@lem300445 A P (@I (nat -> nat) S n)). Qed.
Lemma lem300447 {A : Type'} (y : type1596 A) (n : nat) (x : A) : (term843 A y n x) = (term843 A y n x).
Proof. exact (eq_refl (term843 A y n x)). Qed.
Lemma lem300448 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term852 A P y n x) = (term854 A P y n x).
Proof. exact (MK_COMB (@lem300446 A P n) (@lem300447 A y n x)). Qed.
Lemma lem300450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300451 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300450 A Prop f x). Qed.
Lemma lem300452 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term854 A P y n x) = (term855 A P y n x).
Proof. exact (@lem300451 A (term853 A P n) (term843 A y n x)). Qed.
Lemma lem300453 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term852 A P y n x) = (term855 A P y n x).
Proof. exact (TRANS (@lem300448 A P y n x) (@lem300452 A P y n x)). Qed.
Lemma lem300454 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term851 A P y n x) = (term855 A P y n x).
Proof. exact (TRANS (@lem300442 A P y n x) (@lem300453 A P y n x)). Qed.
Lemma lem300455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300456 {A : Type'} (P : type1597 A) (y : type1596 A) (n : nat) (x : A) : (term856 A P y n x) = (term857 A P y n x).
Proof. exact (MK_COMB (@lem300455) (@lem300454 A P y n x)). Qed.
Lemma lem300457 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term858 A P R y n x) = (term859 A P R y n x).
Proof. exact (MK_COMB (@lem300456 A P y n x) (@lem300414 A R y n x)). Qed.
Lemma lem300458 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem300465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300466 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300465 nat (A -> Prop) f x). Qed.
Lemma lem300467 {A : Type'} (P : type1597 A) (n : nat) : (P n) = (@I (nat -> A -> Prop) P n).
Proof. exact (@lem300466 A P n). Qed.
Lemma lem300468 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem300469 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (P n x) = (@I (nat -> A -> Prop) P n x).
Proof. exact (MK_COMB (@lem300467 A P n) (@lem300468 A x)). Qed.
Lemma lem300471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300472 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300471 A Prop f x). Qed.
Lemma lem300473 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (@I (nat -> A -> Prop) P n x) = (term860 A P n x).
Proof. exact (@lem300472 A (@I (nat -> A -> Prop) P n) x). Qed.
Lemma lem300475 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (P n x) = (term860 A P n x).
Proof. exact (TRANS (@lem300469 A P n x) (@lem300473 A P n x)). Qed.
Lemma lem300476 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term127 A P n x) = (term861 A P n x).
Proof. exact (MK_COMB (@lem300458) (@lem300475 A P n x)). Qed.
Lemma lem300477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300478 {A : Type'} (P : type1597 A) (n : nat) (x : A) : (term62 A P n x) = (term862 A P n x).
Proof. exact (MK_COMB (@lem300477) (@lem300476 A P n x)). Qed.
Lemma lem300479 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term863 A P R y n x) = (term864 A P R y n x).
Proof. exact (MK_COMB (@lem300478 A P n x) (@lem300457 A P R y n x)). Qed.
Lemma lem300480 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term865 A P R y n) = (term866 A P R y n).
Proof. exact (fun_ext (fun x : A => @lem300479 A P R y n x)). Qed.
Lemma lem300481 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300482 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term182 A P R y n) = (term867 A P R y n).
Proof. exact (MK_COMB (@lem300481 A) (@lem300480 A P R y n)). Qed.
Lemma lem300483 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term184 A P R y) = (term868 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem300482 A P R y n)). Qed.
Lemma lem300484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300485 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term186 A P R y) = (term869 A P R y).
Proof. exact (MK_COMB (@lem300484) (@lem300483 A P R y)). Qed.
Lemma lem300486 {A : Type'} (P : type1597 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem300491 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300492 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem300491 nat nat f x). Qed.
Lemma lem300494 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem300492 NUMERAL 0). Qed.
Lemma lem300495 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300496 {A : Type'} (P : type1597 A) : (term784 A P) = (term785 A P).
Proof. exact (MK_COMB (@lem300486 A P) (@lem300494)). Qed.
Lemma lem300497 {A : Type'} (P : type1597 A) (a : A) : (term52 A P a) = (term786 A P a).
Proof. exact (MK_COMB (@lem300496 A P) (@lem300495 A a)). Qed.
Lemma lem300499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300500 {A : Type'} (f : type1597 A) (x : nat) : (f x) = (@I (nat -> A -> Prop) f x).
Proof. exact (@lem300499 nat (A -> Prop) f x). Qed.
Lemma lem300501 {A : Type'} (P : type1597 A) : (term785 A P) = (term787 A P).
Proof. exact (@lem300500 A P (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem300502 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem300503 {A : Type'} (P : type1597 A) (a : A) : (term786 A P a) = (term788 A P a).
Proof. exact (MK_COMB (@lem300501 A P) (@lem300502 A a)). Qed.
Lemma lem300505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem300506 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem300505 A Prop f x). Qed.
Lemma lem300507 {A : Type'} (P : type1597 A) (a : A) : (term788 A P a) = (term789 A P a).
Proof. exact (@lem300506 A (term787 A P) a). Qed.
Lemma lem300508 {A : Type'} (P : type1597 A) (a : A) : (term786 A P a) = (term789 A P a).
Proof. exact (TRANS (@lem300503 A P a) (@lem300507 A P a)). Qed.
Lemma lem300509 {A : Type'} (P : type1597 A) (a : A) : (term52 A P a) = (term789 A P a).
Proof. exact (TRANS (@lem300497 A P a) (@lem300508 A P a)). Qed.
Lemma lem300510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300511 {A : Type'} (P : type1597 A) (a : A) : (term41 A P a) = (term870 A P a).
Proof. exact (MK_COMB (@lem300510) (@lem300509 A P a)). Qed.
Lemma lem300512 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term219 A a P R y) = (term871 A a P R y).
Proof. exact (MK_COMB (@lem300511 A P a) (@lem300485 A P R y)). Qed.
Lemma lem300513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300514 {A : Type'} (a : A) (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term300 A a P R y) = (term872 A a P R y).
Proof. exact (MK_COMB (@lem300513) (@lem300512 A a P R y)). Qed.
Lemma lem300515 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) : (term316 A a y P R n') = (term873 A a y P R n').
Proof. exact (MK_COMB (@lem300514 A a P R y) (@lem300372 A P R n')). Qed.
Lemma lem300516 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term873 A a y P R n'.
Proof. exact (EQ_MP (@lem300515 A a y P R n') (@lem299799 A a y P R n' h1)). Qed.
Lemma lem300517 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term842 A P R n'.
Proof. exact (proj2 (@lem300516 A a y P R n' h1)). Qed.
Lemma lem300518 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term871 A a P R y.
Proof. exact (proj1 (@lem300516 A a y P R n' h1)). Qed.
Lemma lem300519 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term869 A P R y.
Proof. exact (proj2 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem300522 {A : Type'} (P : Prop) (Q : A -> Prop) : (term874 A P Q) = (term875 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem300523 {A : Type'} (P : Prop) (Q : A -> Prop) : (term874 A P Q) = (term875 A P Q).
Proof. exact (@lem300522 A P Q). Qed.
Lemma lem300524 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term876 A n x P R a) = (term877 A n x P R a).
Proof. exact (@lem300523 A (term779 A n x P R a) (term770 A n x P R a)). Qed.
Lemma lem300525 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term878 A n x P R a y) = (term768 A n x P R a y).
Proof. exact (eq_refl (term878 A n x P R a y)). Qed.
Lemma lem300526 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term879 A n x P R a) = (term770 A n x P R a).
Proof. exact (fun_ext (fun y : A => @lem300525 A n x P R a y)). Qed.
Lemma lem300527 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300528 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term880 A n x P R a) = (term772 A n x P R a).
Proof. exact (MK_COMB (@lem300527 A) (@lem300526 A n x P R a)). Qed.
Lemma lem300529 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term781 A n x P R a) = (term781 A n x P R a).
Proof. exact (eq_refl (term781 A n x P R a)). Qed.
Lemma lem300530 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term876 A n x P R a) = (term783 A n x P R a).
Proof. exact (MK_COMB (@lem300529 A n x P R a) (@lem300528 A n x P R a)). Qed.
Lemma lem300531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem300532 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term881 A n x P R a) = (term882 A n x P R a).
Proof. exact (MK_COMB (@lem300531) (@lem300530 A n x P R a)). Qed.
Lemma lem300533 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term878 A n x P R a y) = (term768 A n x P R a y).
Proof. exact (eq_refl (term878 A n x P R a y)). Qed.
Lemma lem300534 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term781 A n x P R a) = (term781 A n x P R a).
Proof. exact (eq_refl (term781 A n x P R a)). Qed.
Lemma lem300535 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term883 A n x P R a y) = (term884 A n x P R a y).
Proof. exact (MK_COMB (@lem300534 A n x P R a) (@lem300533 A n x P R a y)). Qed.
Lemma lem300536 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term885 A n x P R a) = (term886 A n x P R a).
Proof. exact (fun_ext (fun y : A => @lem300535 A n x P R a y)). Qed.
Lemma lem300537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300538 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term877 A n x P R a) = (term887 A n x P R a).
Proof. exact (MK_COMB (@lem300537 A) (@lem300536 A n x P R a)). Qed.
Lemma lem300539 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term876 A n x P R a) = (term877 A n x P R a)) = ((term783 A n x P R a) = (term887 A n x P R a)).
Proof. exact (MK_COMB (@lem300532 A n x P R a) (@lem300538 A n x P R a)). Qed.
Lemma lem300540 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term783 A n x P R a) = (term887 A n x P R a).
Proof. exact (EQ_MP (@lem300539 A n x P R a) (@lem300524 A n x P R a)). Qed.
Lemma lem300541 {A : Type'} (P : type1597 A) (a : A) : (term791 A P a) = (term791 A P a).
Proof. exact (eq_refl (term791 A P a)). Qed.
Lemma lem300542 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term793 A n x P R a) = (term888 A n x P R a).
Proof. exact (MK_COMB (@lem300541 A P a) (@lem300540 A n x P R a)). Qed.
Lemma lem300544 {A : Type'} (P : Prop) (Q : A -> Prop) : (term889 A P Q) = (term890 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem300545 {A : Type'} (P : Prop) (Q : A -> Prop) : (term889 A P Q) = (term890 A P Q).
Proof. exact (@lem300544 A P Q). Qed.
Lemma lem300546 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term891 A n x P R a) = (term892 A n x P R a).
Proof. exact (@lem300545 A (term790 A P a) (term886 A n x P R a)). Qed.
Lemma lem300547 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term893 A n x P R a y) = (term884 A n x P R a y).
Proof. exact (eq_refl (term893 A n x P R a y)). Qed.
Lemma lem300548 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term894 A n x P R a) = (term886 A n x P R a).
Proof. exact (fun_ext (fun y : A => @lem300547 A n x P R a y)). Qed.
Lemma lem300549 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300550 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term895 A n x P R a) = (term887 A n x P R a).
Proof. exact (MK_COMB (@lem300549 A) (@lem300548 A n x P R a)). Qed.
Lemma lem300551 {A : Type'} (P : type1597 A) (a : A) : (term791 A P a) = (term791 A P a).
Proof. exact (eq_refl (term791 A P a)). Qed.
Lemma lem300552 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term891 A n x P R a) = (term888 A n x P R a).
Proof. exact (MK_COMB (@lem300551 A P a) (@lem300550 A n x P R a)). Qed.
Lemma lem300553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem300554 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term896 A n x P R a) = (term897 A n x P R a).
Proof. exact (MK_COMB (@lem300553) (@lem300552 A n x P R a)). Qed.
Lemma lem300555 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term893 A n x P R a y) = (term884 A n x P R a y).
Proof. exact (eq_refl (term893 A n x P R a y)). Qed.
Lemma lem300556 {A : Type'} (P : type1597 A) (a : A) : (term791 A P a) = (term791 A P a).
Proof. exact (eq_refl (term791 A P a)). Qed.
Lemma lem300557 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term898 A n x P R a y) = (term899 A n x P R a y).
Proof. exact (MK_COMB (@lem300556 A P a) (@lem300555 A n x P R a y)). Qed.
Lemma lem300558 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term900 A n x P R a) = (term901 A n x P R a).
Proof. exact (fun_ext (fun y : A => @lem300557 A n x P R a y)). Qed.
Lemma lem300559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300560 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term892 A n x P R a) = (term902 A n x P R a).
Proof. exact (MK_COMB (@lem300559 A) (@lem300558 A n x P R a)). Qed.
Lemma lem300561 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term891 A n x P R a) = (term892 A n x P R a)) = ((term888 A n x P R a) = (term902 A n x P R a)).
Proof. exact (MK_COMB (@lem300554 A n x P R a) (@lem300560 A n x P R a)). Qed.
Lemma lem300562 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term888 A n x P R a) = (term902 A n x P R a).
Proof. exact (EQ_MP (@lem300561 A n x P R a) (@lem300546 A n x P R a)). Qed.
Lemma lem300563 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term793 A n x P R a) = (term902 A n x P R a).
Proof. exact (TRANS (@lem300542 A n x P R a) (@lem300562 A n x P R a)). Qed.
Lemma lem300564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300565 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term795 A n x P R a) = (term903 A n x P R a).
Proof. exact (MK_COMB (@lem300564) (@lem300563 A n x P R a)). Qed.
Lemma lem300567 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term904 A P Q) = (term905 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem300568 (P : nat -> Prop) (Q : nat -> Prop) : (term906 P Q) = (term907 P Q).
Proof. exact (@lem300567 nat P Q). Qed.
Lemma lem300569 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term908 A f P R a) = (term909 A f P R a).
Proof. exact (@lem300568 (term717 A f P R a) (term709 A f P R a)). Qed.
Lemma lem300570 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term910 A f P R a n) = (term715 A f P R a n).
Proof. exact (eq_refl (term910 A f P R a n)). Qed.
Lemma lem300571 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term911 A f P R a) = (term717 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem300570 A f P R a n)). Qed.
Lemma lem300572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300573 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term912 A f P R a) = (term719 A f P R a).
Proof. exact (MK_COMB (@lem300572) (@lem300571 A f P R a)). Qed.
Lemma lem300574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300575 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term913 A f P R a) = (term721 A f P R a).
Proof. exact (MK_COMB (@lem300574) (@lem300573 A f P R a)). Qed.
Lemma lem300576 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term914 A f P R a n) = (term707 A f P R a n).
Proof. exact (eq_refl (term914 A f P R a n)). Qed.
Lemma lem300577 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term915 A f P R a) = (term709 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem300576 A f P R a n)). Qed.
Lemma lem300578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300579 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term916 A f P R a) = (term711 A f P R a).
Proof. exact (MK_COMB (@lem300578) (@lem300577 A f P R a)). Qed.
Lemma lem300580 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term908 A f P R a) = (term723 A f P R a).
Proof. exact (MK_COMB (@lem300575 A f P R a) (@lem300579 A f P R a)). Qed.
Lemma lem300581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem300582 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term917 A f P R a) = (term918 A f P R a).
Proof. exact (MK_COMB (@lem300581) (@lem300580 A f P R a)). Qed.
Lemma lem300583 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term910 A f P R a n) = (term715 A f P R a n).
Proof. exact (eq_refl (term910 A f P R a n)). Qed.
Lemma lem300584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300585 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term919 A f P R a n) = (term920 A f P R a n).
Proof. exact (MK_COMB (@lem300584) (@lem300583 A f P R a n)). Qed.
Lemma lem300586 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term914 A f P R a n) = (term707 A f P R a n).
Proof. exact (eq_refl (term914 A f P R a n)). Qed.
Lemma lem300587 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term921 A f P R a n) = (term922 A f P R a n).
Proof. exact (MK_COMB (@lem300585 A f P R a n) (@lem300586 A f P R a n)). Qed.
Lemma lem300588 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term923 A f P R a) = (term924 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem300587 A f P R a n)). Qed.
Lemma lem300589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300590 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term909 A f P R a) = (term925 A f P R a).
Proof. exact (MK_COMB (@lem300589) (@lem300588 A f P R a)). Qed.
Lemma lem300591 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term908 A f P R a) = (term909 A f P R a)) = ((term723 A f P R a) = (term925 A f P R a)).
Proof. exact (MK_COMB (@lem300582 A f P R a) (@lem300590 A f P R a)). Qed.
Lemma lem300592 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term723 A f P R a) = (term925 A f P R a).
Proof. exact (EQ_MP (@lem300591 A f P R a) (@lem300569 A f P R a)). Qed.
Lemma lem300593 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term731 A f P R a) = (term731 A f P R a).
Proof. exact (eq_refl (term731 A f P R a)). Qed.
Lemma lem300594 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term733 A f P R a) = (term926 A f P R a).
Proof. exact (MK_COMB (@lem300593 A f P R a) (@lem300592 A f P R a)). Qed.
Lemma lem300596 {A : Type'} (P : Prop) (Q : A -> Prop) : (term874 A P Q) = (term875 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem300597 (P : Prop) (Q : nat -> Prop) : (term927 P Q) = (term928 P Q).
Proof. exact (@lem300596 nat P Q). Qed.
Lemma lem300598 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term929 A f P R a) = (term930 A f P R a).
Proof. exact (@lem300597 ((term727 A f P R a) = a) (term924 A f P R a)). Qed.
Lemma lem300599 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term931 A f P R a n) = (term922 A f P R a n).
Proof. exact (eq_refl (term931 A f P R a n)). Qed.
Lemma lem300600 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term932 A f P R a) = (term924 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem300599 A f P R a n)). Qed.
Lemma lem300601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300602 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term933 A f P R a) = (term925 A f P R a).
Proof. exact (MK_COMB (@lem300601) (@lem300600 A f P R a)). Qed.
Lemma lem300603 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term731 A f P R a) = (term731 A f P R a).
Proof. exact (eq_refl (term731 A f P R a)). Qed.
Lemma lem300604 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term929 A f P R a) = (term926 A f P R a).
Proof. exact (MK_COMB (@lem300603 A f P R a) (@lem300602 A f P R a)). Qed.
Lemma lem300605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem300606 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term934 A f P R a) = (term935 A f P R a).
Proof. exact (MK_COMB (@lem300605) (@lem300604 A f P R a)). Qed.
Lemma lem300607 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term931 A f P R a n) = (term922 A f P R a n).
Proof. exact (eq_refl (term931 A f P R a n)). Qed.
Lemma lem300608 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term731 A f P R a) = (term731 A f P R a).
Proof. exact (eq_refl (term731 A f P R a)). Qed.
Lemma lem300609 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term936 A f P R a n) = (term937 A f P R a n).
Proof. exact (MK_COMB (@lem300608 A f P R a) (@lem300607 A f P R a n)). Qed.
Lemma lem300610 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term938 A f P R a) = (term939 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem300609 A f P R a n)). Qed.
Lemma lem300611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300612 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term930 A f P R a) = (term940 A f P R a).
Proof. exact (MK_COMB (@lem300611) (@lem300610 A f P R a)). Qed.
Lemma lem300613 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term929 A f P R a) = (term930 A f P R a)) = ((term926 A f P R a) = (term940 A f P R a)).
Proof. exact (MK_COMB (@lem300606 A f P R a) (@lem300612 A f P R a)). Qed.
Lemma lem300614 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term926 A f P R a) = (term940 A f P R a).
Proof. exact (EQ_MP (@lem300613 A f P R a) (@lem300598 A f P R a)). Qed.
Lemma lem300615 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term733 A f P R a) = (term940 A f P R a).
Proof. exact (TRANS (@lem300594 A f P R a) (@lem300614 A f P R a)). Qed.
Lemma lem300616 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term797 A n x f P R a) = (term941 A n x f P R a).
Proof. exact (MK_COMB (@lem300565 A n x P R a) (@lem300615 A f P R a)). Qed.
Lemma lem300618 {A : Type'} (P : A -> Prop) (Q : Prop) : (term942 A P Q) = (term943 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem300619 {A : Type'} (P : A -> Prop) (Q : Prop) : (term942 A P Q) = (term943 A P Q).
Proof. exact (@lem300618 A P Q). Qed.
Lemma lem300620 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term944 A n x f P R a) = (term945 A n x f P R a).
Proof. exact (@lem300619 A (term901 A n x P R a) (term940 A f P R a)). Qed.
Lemma lem300621 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term946 A n x P R a y) = (term899 A n x P R a y).
Proof. exact (eq_refl (term946 A n x P R a y)). Qed.
Lemma lem300622 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term947 A n x P R a) = (term901 A n x P R a).
Proof. exact (fun_ext (fun y : A => @lem300621 A n x P R a y)). Qed.
Lemma lem300623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300624 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term948 A n x P R a) = (term902 A n x P R a).
Proof. exact (MK_COMB (@lem300623 A) (@lem300622 A n x P R a)). Qed.
Lemma lem300625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300626 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term949 A n x P R a) = (term903 A n x P R a).
Proof. exact (MK_COMB (@lem300625) (@lem300624 A n x P R a)). Qed.
Lemma lem300627 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term940 A f P R a) = (term940 A f P R a).
Proof. exact (eq_refl (term940 A f P R a)). Qed.
Lemma lem300628 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term944 A n x f P R a) = (term941 A n x f P R a).
Proof. exact (MK_COMB (@lem300626 A n x P R a) (@lem300627 A f P R a)). Qed.
Lemma lem300629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem300630 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term950 A n x f P R a) = (term951 A n x f P R a).
Proof. exact (MK_COMB (@lem300629) (@lem300628 A n x f P R a)). Qed.
Lemma lem300631 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term946 A n x P R a y) = (term899 A n x P R a y).
Proof. exact (eq_refl (term946 A n x P R a y)). Qed.
Lemma lem300632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300633 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term952 A n x P R a y) = (term953 A n x P R a y).
Proof. exact (MK_COMB (@lem300632) (@lem300631 A n x P R a y)). Qed.
Lemma lem300634 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term940 A f P R a) = (term940 A f P R a).
Proof. exact (eq_refl (term940 A f P R a)). Qed.
Lemma lem300635 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term954 A n x y f P R a) = (term955 A n x y f P R a).
Proof. exact (MK_COMB (@lem300633 A n x P R a y) (@lem300634 A f P R a)). Qed.
Lemma lem300636 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term956 A n x f P R a) = (term957 A n x f P R a).
Proof. exact (fun_ext (fun y : A => @lem300635 A n x y f P R a)). Qed.
Lemma lem300637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300638 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term945 A n x f P R a) = (term958 A n x f P R a).
Proof. exact (MK_COMB (@lem300637 A) (@lem300636 A n x f P R a)). Qed.
Lemma lem300639 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term944 A n x f P R a) = (term945 A n x f P R a)) = ((term941 A n x f P R a) = (term958 A n x f P R a)).
Proof. exact (MK_COMB (@lem300630 A n x f P R a) (@lem300638 A n x f P R a)). Qed.
Lemma lem300640 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term941 A n x f P R a) = (term958 A n x f P R a).
Proof. exact (EQ_MP (@lem300639 A n x f P R a) (@lem300620 A n x f P R a)). Qed.
Lemma lem300642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term889 A P Q) = (term890 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem300643 (P : Prop) (Q : nat -> Prop) : (term959 P Q) = (term960 P Q).
Proof. exact (@lem300642 nat P Q). Qed.
Lemma lem300644 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term961 A n x y f P R a) = (term962 A n x y f P R a).
Proof. exact (@lem300643 (term899 A n x P R a y) (term939 A f P R a)). Qed.
Lemma lem300645 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term963 A f P R a n) = (term937 A f P R a n).
Proof. exact (eq_refl (term963 A f P R a n)). Qed.
Lemma lem300646 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term964 A f P R a) = (term939 A f P R a).
Proof. exact (fun_ext (fun n : nat => @lem300645 A f P R a n)). Qed.
Lemma lem300647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300648 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term965 A f P R a) = (term940 A f P R a).
Proof. exact (MK_COMB (@lem300647) (@lem300646 A f P R a)). Qed.
Lemma lem300649 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term953 A n x P R a y) = (term953 A n x P R a y).
Proof. exact (eq_refl (term953 A n x P R a y)). Qed.
Lemma lem300650 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term961 A n x y f P R a) = (term955 A n x y f P R a).
Proof. exact (MK_COMB (@lem300649 A n x P R a y) (@lem300648 A f P R a)). Qed.
Lemma lem300651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem300652 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term966 A n x y f P R a) = (term967 A n x y f P R a).
Proof. exact (MK_COMB (@lem300651) (@lem300650 A n x y f P R a)). Qed.
Lemma lem300653 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term963 A f P R a n) = (term937 A f P R a n).
Proof. exact (eq_refl (term963 A f P R a n)). Qed.
Lemma lem300654 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term953 A n x P R a y) = (term953 A n x P R a y).
Proof. exact (eq_refl (term953 A n x P R a y)). Qed.
Lemma lem300655 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term968 A n x y f P R a n') = (term969 A n x y f P R a n').
Proof. exact (MK_COMB (@lem300654 A n x P R a y) (@lem300653 A f P R a n')). Qed.
Lemma lem300656 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term970 A n x y f P R a) = (term971 A n x y f P R a).
Proof. exact (fun_ext (fun n' : nat => @lem300655 A n x y f P R a n')). Qed.
Lemma lem300657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300658 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term962 A n x y f P R a) = (term972 A n x y f P R a).
Proof. exact (MK_COMB (@lem300657) (@lem300656 A n x y f P R a)). Qed.
Lemma lem300659 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : ((term961 A n x y f P R a) = (term962 A n x y f P R a)) = ((term955 A n x y f P R a) = (term972 A n x y f P R a)).
Proof. exact (MK_COMB (@lem300652 A n x y f P R a) (@lem300658 A n x y f P R a)). Qed.
Lemma lem300660 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term955 A n x y f P R a) = (term972 A n x y f P R a).
Proof. exact (EQ_MP (@lem300659 A n x y f P R a) (@lem300644 A n x y f P R a)). Qed.
Lemma lem300661 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term957 A n x f P R a) = (term973 A n x f P R a).
Proof. exact (fun_ext (fun y : A => @lem300660 A n x y f P R a)). Qed.
Lemma lem300662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300663 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term958 A n x f P R a) = (term974 A n x f P R a).
Proof. exact (MK_COMB (@lem300662 A) (@lem300661 A n x f P R a)). Qed.
Lemma lem300664 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term941 A n x f P R a) = (term974 A n x f P R a).
Proof. exact (TRANS (@lem300640 A n x f P R a) (@lem300663 A n x f P R a)). Qed.
Lemma lem300665 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term797 A n x f P R a) = (term974 A n x f P R a).
Proof. exact (TRANS (@lem300616 A n x f P R a) (@lem300664 A n x f P R a)). Qed.
Lemma lem300666 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) : (term799 A n x f P R) = (term975 A n x f P R).
Proof. exact (fun_ext (fun a : A => @lem300665 A n x f P R a)). Qed.
Lemma lem300667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300668 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) : (term801 A n x f P R) = (term976 A n x f P R).
Proof. exact (MK_COMB (@lem300667 A) (@lem300666 A n x f P R)). Qed.
Lemma lem300669 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term803 A n x f P) = (term977 A n x f P).
Proof. exact (fun_ext (fun R : type1594 A => @lem300668 A n x f P R)). Qed.
Lemma lem300670 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem300671 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term804 A n x f P) = (term978 A n x f P).
Proof. exact (MK_COMB (@lem300670 A) (@lem300669 A n x f P)). Qed.
Lemma lem300672 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term805 A n x f) = (term979 A n x f).
Proof. exact (fun_ext (fun P : type1597 A => @lem300671 A n x f P)). Qed.
Lemma lem300673 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem300674 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term806 A n x f) = (term980 A n x f).
Proof. exact (MK_COMB (@lem300673 A) (@lem300672 A n x f)). Qed.
Lemma lem300683 {A : Type'} (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n : nat) : (term937 A f P R a n) = (term937 A f P R a n).
Proof. exact (eq_refl (term937 A f P R a n)). Qed.
Lemma lem300706 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term899 A n x P R a y) = (term981 A n x P R a y).
Proof. exact (@lem19490 (term779 A n x P R a) (term790 A P a) (term768 A n x P R a y)). Qed.
Lemma lem300707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem300708 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) (y : A) : (term953 A n x P R a y) = (term982 A n x P R a y).
Proof. exact (MK_COMB (@lem300707) (@lem300706 A n x P R a y)). Qed.
Lemma lem300709 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term969 A n x y f P R a n') = (term983 A n x y f P R a n').
Proof. exact (MK_COMB (@lem300708 A n x P R a y) (@lem300683 A f P R a n')). Qed.
Lemma lem300710 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term983 A n x y f P R a n') = (term984 A n x y f P R a n').
Proof. exact (@lem19490 ((term727 A f P R a) = a) (term981 A n x P R a y) (term922 A f P R a n')). Qed.
Lemma lem300711 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term985 A n x y f P R a n') = (term986 A n x y f P R a n').
Proof. exact (@lem19490 (term715 A f P R a n') (term981 A n x P R a y) (term707 A f P R a n')). Qed.
Lemma lem300718 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term987 A n x y f P R a n') = (term988 A n x y f P R a n').
Proof. exact (@lem19699 (term989 A n x P R a) (term990 A n x P R a y) (term707 A f P R a n')). Qed.
Lemma lem300725 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term991 A n x y f P R a n') = (term992 A n x y f P R a n').
Proof. exact (@lem19699 (term989 A n x P R a) (term990 A n x P R a y) (term715 A f P R a n')). Qed.
Lemma lem300726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300727 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term993 A n x y f P R a n') = (term994 A n x y f P R a n').
Proof. exact (MK_COMB (@lem300726) (@lem300725 A n x y f P R a n')). Qed.
Lemma lem300728 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term986 A n x y f P R a n') = (term995 A n x y f P R a n').
Proof. exact (MK_COMB (@lem300727 A n x y f P R a n') (@lem300718 A n x y f P R a n')). Qed.
Lemma lem300729 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term985 A n x y f P R a n') = (term995 A n x y f P R a n').
Proof. exact (TRANS (@lem300711 A n x y f P R a n') (@lem300728 A n x y f P R a n')). Qed.
Lemma lem300736 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term996 A n x y f P R a) = (term997 A n x y f P R a).
Proof. exact (@lem19699 (term989 A n x P R a) (term990 A n x P R a y) ((term727 A f P R a) = a)). Qed.
Lemma lem300737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem300738 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term998 A n x y f P R a) = (term999 A n x y f P R a).
Proof. exact (MK_COMB (@lem300737) (@lem300736 A n x y f P R a)). Qed.
Lemma lem300739 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term984 A n x y f P R a n') = (term1000 A n x y f P R a n').
Proof. exact (MK_COMB (@lem300738 A n x y f P R a) (@lem300729 A n x y f P R a n')). Qed.
Lemma lem300740 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term983 A n x y f P R a n') = (term1000 A n x y f P R a n').
Proof. exact (TRANS (@lem300710 A n x y f P R a n') (@lem300739 A n x y f P R a n')). Qed.
Lemma lem300741 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (n' : nat) : (term969 A n x y f P R a n') = (term1000 A n x y f P R a n').
Proof. exact (TRANS (@lem300709 A n x y f P R a n') (@lem300740 A n x y f P R a n')). Qed.
Lemma lem300742 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term971 A n x y f P R a) = (term1001 A n x y f P R a).
Proof. exact (fun_ext (fun n' : nat => @lem300741 A n x y f P R a n')). Qed.
Lemma lem300743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300744 {A : Type'} (n : type946 A) (x : type945 A) (y : A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term972 A n x y f P R a) = (term1002 A n x y f P R a).
Proof. exact (MK_COMB (@lem300743) (@lem300742 A n x y f P R a)). Qed.
Lemma lem300745 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term973 A n x f P R a) = (term1003 A n x f P R a).
Proof. exact (fun_ext (fun y : A => @lem300744 A n x y f P R a)). Qed.
Lemma lem300746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300747 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term974 A n x f P R a) = (term1004 A n x f P R a).
Proof. exact (MK_COMB (@lem300746 A) (@lem300745 A n x f P R a)). Qed.
Lemma lem300748 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) : (term975 A n x f P R) = (term1005 A n x f P R).
Proof. exact (fun_ext (fun a : A => @lem300747 A n x f P R a)). Qed.
Lemma lem300749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300750 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) : (term976 A n x f P R) = (term1006 A n x f P R).
Proof. exact (MK_COMB (@lem300749 A) (@lem300748 A n x f P R)). Qed.
Lemma lem300751 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term977 A n x f P) = (term1007 A n x f P).
Proof. exact (fun_ext (fun R : type1594 A => @lem300750 A n x f P R)). Qed.
Lemma lem300752 {A : Type'} : (@all (nat -> A -> A -> Prop)) = (@all (nat -> A -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> A -> Prop))). Qed.
Lemma lem300753 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) : (term978 A n x f P) = (term1008 A n x f P).
Proof. exact (MK_COMB (@lem300752 A) (@lem300751 A n x f P)). Qed.
Lemma lem300754 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term979 A n x f) = (term1009 A n x f).
Proof. exact (fun_ext (fun P : type1597 A => @lem300753 A n x f P)). Qed.
Lemma lem300755 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem300756 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term980 A n x f) = (term1010 A n x f).
Proof. exact (MK_COMB (@lem300755 A) (@lem300754 A n x f)). Qed.
Lemma lem300757 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) : (term806 A n x f) = (term1010 A n x f).
Proof. exact (TRANS (@lem300674 A n x f) (@lem300756 A n x f)). Qed.
Lemma lem300758 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1010 A n x f.
Proof. exact (EQ_MP (@lem300757 A n x f) (@lem300256 A n x f h1)). Qed.
Lemma lem300766 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) (f : nat -> A) : (term840 A P R n' f) = (term840 A P R n' f).
Proof. exact (eq_refl (term840 A P R n' f)). Qed.
Lemma lem300767 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) : (term841 A P R n') = (term841 A P R n').
Proof. exact (fun_ext (fun f : nat -> A => @lem300766 A P R n' f)). Qed.
Lemma lem300768 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem300770 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) : (term842 A P R n') = (term842 A P R n').
Proof. exact (MK_COMB (@lem300768 A) (@lem300767 A P R n')). Qed.
Lemma lem300771 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term842 A P R n'.
Proof. exact (EQ_MP (@lem300770 A P R n') (@lem300517 A a y P R n' h1)). Qed.
Lemma lem300793 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) (x : A) : (term864 A P R y n x) = (term1011 A P R y n x).
Proof. exact (@lem19490 (term855 A P y n x) (term861 A P n x) (term848 A R y n x)). Qed.
Lemma lem300794 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term866 A P R y n) = (term1012 A P R y n).
Proof. exact (fun_ext (fun x : A => @lem300793 A P R y n x)). Qed.
Lemma lem300795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem300796 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (n : nat) : (term867 A P R y n) = (term1013 A P R y n).
Proof. exact (MK_COMB (@lem300795 A) (@lem300794 A P R y n)). Qed.
Lemma lem300797 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term868 A P R y) = (term1014 A P R y).
Proof. exact (fun_ext (fun n : nat => @lem300796 A P R y n)). Qed.
Lemma lem300798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem300800 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) : (term869 A P R y) = (term1015 A P R y).
Proof. exact (MK_COMB (@lem300798) (@lem300797 A P R y)). Qed.
Lemma lem300801 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1015 A P R y.
Proof. exact (EQ_MP (@lem300800 A P R y) (@lem300519 A a y P R n' h1)). Qed.
Lemma lem300802 {A : Type'} (_6684 : type1597 A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1016 A n x f _6684.
Proof. exact (@lem300758 A n x f h1 _6684). Qed.
Lemma lem300803 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) : (term1016 A n x f _6684) = (term1008 A n x f _6684).
Proof. exact (eq_refl (term1016 A n x f _6684)). Qed.
Lemma lem300804 {A : Type'} (_6684 : type1597 A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1008 A n x f _6684.
Proof. exact (EQ_MP (@lem300803 A n x f _6684) (@lem300802 A _6684 n x f h1)). Qed.
Lemma lem300805 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1017 A n x f _6684 _6685.
Proof. exact (@lem300804 A _6684 n x f h1 _6685). Qed.
Lemma lem300806 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) : (term1017 A n x f _6684 _6685) = (term1006 A n x f _6684 _6685).
Proof. exact (eq_refl (term1017 A n x f _6684 _6685)). Qed.
Lemma lem300807 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1006 A n x f _6684 _6685.
Proof. exact (EQ_MP (@lem300806 A n x f _6684 _6685) (@lem300805 A _6684 _6685 n x f h1)). Qed.
Lemma lem300808 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1018 A n x f _6684 _6685 _6686.
Proof. exact (@lem300807 A _6684 _6685 n x f h1 _6686). Qed.
Lemma lem300809 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1018 A n x f _6684 _6685 _6686) = (term1004 A n x f _6684 _6685 _6686).
Proof. exact (eq_refl (term1018 A n x f _6684 _6685 _6686)). Qed.
Lemma lem300810 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1004 A n x f _6684 _6685 _6686.
Proof. exact (EQ_MP (@lem300809 A n x f _6684 _6685 _6686) (@lem300808 A _6684 _6685 _6686 n x f h1)). Qed.
Lemma lem300811 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1019 A n x f _6684 _6685 _6686 _6687.
Proof. exact (@lem300810 A _6684 _6685 _6686 n x f h1 _6687). Qed.
Lemma lem300812 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1019 A n x f _6684 _6685 _6686 _6687) = (term1002 A n x _6687 f _6684 _6685 _6686).
Proof. exact (eq_refl (term1019 A n x f _6684 _6685 _6686 _6687)). Qed.
Lemma lem300813 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1002 A n x _6687 f _6684 _6685 _6686.
Proof. exact (EQ_MP (@lem300812 A n x _6687 f _6684 _6685 _6686) (@lem300811 A _6684 _6685 _6686 _6687 n x f h1)). Qed.
Lemma lem300814 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1020 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (@lem300813 A _6687 _6684 _6685 _6686 n x f h1 _6688). Qed.
Lemma lem300815 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1020 A n x _6687 f _6684 _6685 _6686 _6688) = (term1000 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1020 A n x _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300816 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1000 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem300815 A n x _6687 f _6684 _6685 _6686 _6688) (@lem300814 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300817 {A : Type'} (_6689 : nat -> A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1021 A P R n' _6689.
Proof. exact (@lem300771 A a y P R n' h1 _6689). Qed.
Lemma lem300818 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) (_6689 : nat -> A) : (term1021 A P R n' _6689) = (term840 A P R n' _6689).
Proof. exact (eq_refl (term1021 A P R n' _6689)). Qed.
Lemma lem300820 {A : Type'} (_6690 : nat) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1022 A P R y _6690.
Proof. exact (@lem300801 A a y P R n' h1 _6690). Qed.
Lemma lem300821 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6690 : nat) : (term1022 A P R y _6690) = (term1013 A P R y _6690).
Proof. exact (eq_refl (term1022 A P R y _6690)). Qed.
Lemma lem300822 {A : Type'} (_6690 : nat) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1013 A P R y _6690.
Proof. exact (EQ_MP (@lem300821 A P R y _6690) (@lem300820 A _6690 a y P R n' h1)). Qed.
Lemma lem300823 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1023 A P R y _6690 _6691.
Proof. exact (@lem300822 A _6690 a y P R n' h1 _6691). Qed.
Lemma lem300824 {A : Type'} (P : type1597 A) (R : type1594 A) (y : type1596 A) (_6690 : nat) (_6691 : A) : (term1023 A P R y _6690 _6691) = (term1011 A P R y _6690 _6691).
Proof. exact (eq_refl (term1023 A P R y _6690 _6691)). Qed.
Lemma lem300825 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1011 A P R y _6690 _6691.
Proof. exact (EQ_MP (@lem300824 A P R y _6690 _6691) (@lem300823 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem300828 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term995 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (proj2 (@lem300816 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300830 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term988 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (proj2 (@lem300828 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300831 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term992 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (proj1 (@lem300828 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300832 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1024 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (proj2 (@lem300830 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300833 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1025 A n x f _6684 _6685 _6686 _6688.
Proof. exact (proj1 (@lem300830 A (@el A) _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300834 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1026 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (proj2 (@lem300831 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300835 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1027 A n x f _6684 _6685 _6686 _6688.
Proof. exact (proj1 (@lem300831 A (@el A) _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300843 {A : Type'} (_6689 : nat -> A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term840 A P R n' _6689.
Proof. exact (EQ_MP (@lem300818 A P R n' _6689) (@lem300817 A _6689 a y P R n' h1)). Qed.
Lemma lem300851 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1028 A P y _6690 _6691.
Proof. exact (proj1 (@lem300825 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem300857 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1029 A P R y _6690 _6691.
Proof. exact (proj2 (@lem300825 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem300868 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1025 A n x f _6684 _6685 _6686 _6688) = (term1030 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem297919 (term790 A _6684 _6686) (term779 A n x _6684 _6685 _6686) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300869 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1030 A n x f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem300868 A n x f _6684 _6685 _6686 _6688) (@lem300833 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300873 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1024 A n x _6687 f _6684 _6685 _6686 _6688) = (term1031 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem297919 (term790 A _6684 _6686) (term768 A n x _6684 _6685 _6686 _6687) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300880 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1032 A n x _6687 f _6684 _6685 _6686 _6688) = (term1033 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem297919 (term764 A n _6684 _6685 _6686 _6687) (term752 A n x _6684 _6685 _6686 _6687) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300881 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term791 A _6684 _6686) = (term791 A _6684 _6686).
Proof. exact (eq_refl (term791 A _6684 _6686)). Qed.
Lemma lem300884 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1031 A n x _6687 f _6684 _6685 _6686 _6688) = (term1034 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem300881 A _6684 _6686) (@lem300880 A n x _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300886 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1024 A n x _6687 f _6684 _6685 _6686 _6688) = (term1034 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem300873 A n x _6687 f _6684 _6685 _6686 _6688) (@lem300884 A n x _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300887 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1034 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem300886 A n x _6687 f _6684 _6685 _6686 _6688) (@lem300832 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300898 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1027 A n x f _6684 _6685 _6686 _6688) = (term1035 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem297919 (term790 A _6684 _6686) (term779 A n x _6684 _6685 _6686) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300899 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1035 A n x f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem300898 A n x f _6684 _6685 _6686 _6688) (@lem300835 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem300903 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1026 A n x _6687 f _6684 _6685 _6686 _6688) = (term1036 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem297919 (term790 A _6684 _6686) (term768 A n x _6684 _6685 _6686 _6687) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300910 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1037 A n x _6687 f _6684 _6685 _6686 _6688) = (term1038 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem297919 (term764 A n _6684 _6685 _6686 _6687) (term752 A n x _6684 _6685 _6686 _6687) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300911 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term791 A _6684 _6686) = (term791 A _6684 _6686).
Proof. exact (eq_refl (term791 A _6684 _6686)). Qed.
Lemma lem300914 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1036 A n x _6687 f _6684 _6685 _6686 _6688) = (term1039 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem300911 A _6684 _6686) (@lem300910 A n x _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300916 {A : Type'} (n : type946 A) (x : type945 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1026 A n x _6687 f _6684 _6685 _6686 _6688) = (term1039 A n x _6687 f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem300903 A n x _6687 f _6684 _6685 _6686 _6688) (@lem300914 A n x _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem300917 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1039 A n x _6687 f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem300916 A n x _6687 f _6684 _6685 _6686 _6688) (@lem300834 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem301246 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (proj1 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem301247 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1040 A P a.
Proof. exact (fun h0 : term790 A P a => @lem301246 A a y P R n' h1). Qed.
Lemma lem301249 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301250 {A : Type'} (P : type1597 A) (a : A) : (term1040 A P a) = (term789 A P a).
Proof. exact (@lem301249 (term789 A P a)). Qed.
Lemma lem301251 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (EQ_MP (@lem301250 A P a) (@lem301247 A a y P R n' h1)). Qed.
Lemma lem301253 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (proj1 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem301254 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1040 A P a.
Proof. exact (fun h0 : term790 A P a => @lem301253 A a y P R n' h1). Qed.
Lemma lem301256 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301257 {A : Type'} (P : type1597 A) (a : A) : (term1040 A P a) = (term789 A P a).
Proof. exact (@lem301256 (term789 A P a)). Qed.
Lemma lem301258 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (EQ_MP (@lem301257 A P a) (@lem301254 A a y P R n' h1)). Qed.
Lemma lem301260 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (proj1 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem301261 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1040 A P a.
Proof. exact (fun h0 : term790 A P a => @lem301260 A a y P R n' h1). Qed.
Lemma lem301263 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301264 {A : Type'} (P : type1597 A) (a : A) : (term1040 A P a) = (term789 A P a).
Proof. exact (@lem301263 (term789 A P a)). Qed.
Lemma lem301265 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (EQ_MP (@lem301264 A P a) (@lem301261 A a y P R n' h1)). Qed.
Lemma lem301268 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1042 A n' f P R a) : term1042 A n' f P R a.
Proof. exact (h1). Qed.
Lemma lem301269 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1042 A n' f P R a) : term1043 A n' f P R a.
Proof. exact (fun h0 : term1044 A n' f P R a => @lem301268 A n' f P R a h1). Qed.
Lemma lem301271 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem301272 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1043 A n' f P R a) = (term1042 A n' f P R a).
Proof. exact (@lem301271 (term1044 A n' f P R a)). Qed.
Lemma lem301273 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1042 A n' f P R a) : term1042 A n' f P R a.
Proof. exact (EQ_MP (@lem301272 A n' f P R a) (@lem301269 A n' f P R a h1)). Qed.
Lemma lem301279 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301280 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1035 A n x f _6684 _6685 _6686 _6688) = (term1046 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem301279 (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301294 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301295 {A : Type'} (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1047 A f _6684 _6685 _6686 _6688) = (term1048 A f _6685 _6688 _6684 _6686).
Proof. exact (@lem301294 (term715 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686)). Qed.
Lemma lem301301 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1049 A n x _6684 _6685 _6686) = (term1049 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1049 A n x _6684 _6685 _6686)). Qed.
Lemma lem301302 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1050 A n x f _6685 _6688 _6684 _6686).
Proof. exact (MK_COMB (@lem301301 A n x _6684 _6685 _6686) (@lem301295 A f _6685 _6688 _6684 _6686)). Qed.
Lemma lem301306 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301307 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1050 A n x f _6685 _6688 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (@lem301306 (term715 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem301323 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301302 A n x f _6685 _6688 _6684 _6686) (@lem301307 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301324 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1035 A n x f _6684 _6685 _6686 _6688) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301280 A n x f _6684 _6685 _6686 _6688) (@lem301323 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem301326 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1052 A n x f _6684 _6685 _6686 _6688) = (term1053 A f _6688 n x _6685 _6684 _6686).
Proof. exact (MK_COMB (@lem301325) (@lem301324 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301341 {A : Type'} (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1047 A f _6684 _6685 _6686 _6688) = (term1048 A f _6685 _6688 _6684 _6686).
Proof. exact (@lem301340 (term715 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686)). Qed.
Lemma lem301347 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1049 A n x _6684 _6685 _6686) = (term1049 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1049 A n x _6684 _6685 _6686)). Qed.
Lemma lem301348 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1050 A n x f _6685 _6688 _6684 _6686).
Proof. exact (MK_COMB (@lem301347 A n x _6684 _6685 _6686) (@lem301341 A f _6685 _6688 _6684 _6686)). Qed.
Lemma lem301352 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301353 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1050 A n x f _6685 _6688 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (@lem301352 (term715 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem301369 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301348 A n x f _6685 _6688 _6684 _6686) (@lem301353 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301370 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1035 A n x f _6684 _6685 _6686 _6688) = (term1046 A n x f _6684 _6685 _6686 _6688)) = ((term1051 A f _6688 n x _6685 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686)).
Proof. exact (MK_COMB (@lem301326 A f _6688 n x _6685 _6684 _6686) (@lem301369 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301372 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem301373 (x : Prop) : (x = x) = True.
Proof. exact (@lem301372 Prop x). Qed.
Lemma lem301374 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1051 A f _6688 n x _6685 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686)) = True.
Proof. exact (@lem301373 (term1051 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301375 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : ((term1035 A n x f _6684 _6685 _6686 _6688) = (term1046 A n x f _6684 _6685 _6686 _6688)) = True.
Proof. exact (TRANS (@lem301370 A f _6688 n x _6685 _6684 _6686) (@lem301374 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301376 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : True = ((term1035 A n x f _6684 _6685 _6686 _6688) = (term1046 A n x f _6684 _6685 _6686 _6688)).
Proof. exact (SYM (@lem301375 A n x f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301377 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1035 A n x f _6684 _6685 _6686 _6688) = (term1046 A n x f _6684 _6685 _6686 _6688).
Proof. exact (EQ_MP (@lem301376 A n x f _6684 _6685 _6686 _6688) (@lem0)). Qed.
Lemma lem301378 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1046 A n x f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem301377 A n x f _6684 _6685 _6686 _6688) (@lem300899 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem301380 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem301381 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1055 A f _6688 n x _6684 _6685 _6686).
Proof. exact (@lem301380 (term1047 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686)). Qed.
Lemma lem301383 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem301384 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1058 A f _6684 _6685 _6686 _6688) = (term1059 A f _6684 _6685 _6686 _6688).
Proof. exact (@lem301383 (term790 A _6684 _6686) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301386 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem301387 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1061 A _6684 _6686) = (term789 A _6684 _6686).
Proof. exact (@lem301386 (term789 A _6684 _6686)). Qed.
Lemma lem301388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem301389 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1062 A _6684 _6686) = (term870 A _6684 _6686).
Proof. exact (MK_COMB (@lem301388) (@lem301387 A _6684 _6686)). Qed.
Lemma lem301390 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1063 A f _6684 _6685 _6686 _6688) = (term1063 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1063 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301391 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1059 A f _6684 _6685 _6686 _6688) = (term1064 A f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem301389 A _6684 _6686) (@lem301390 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301392 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1058 A f _6684 _6685 _6686 _6688) = (term1064 A f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem301384 A f _6684 _6685 _6686 _6688) (@lem301391 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem301394 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1065 A f _6684 _6685 _6686 _6688) = (term1066 A f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem301393) (@lem301392 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301395 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term779 A n x _6684 _6685 _6686) = (term779 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term779 A n x _6684 _6685 _6686)). Qed.
Lemma lem301396 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1055 A f _6688 n x _6684 _6685 _6686) = (term1067 A f _6688 n x _6684 _6685 _6686).
Proof. exact (MK_COMB (@lem301394 A f _6684 _6685 _6686 _6688) (@lem301395 A n x _6684 _6685 _6686)). Qed.
Lemma lem301397 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1067 A f _6688 n x _6684 _6685 _6686).
Proof. exact (TRANS (@lem301381 A f _6688 n x _6684 _6685 _6686) (@lem301396 A f _6688 n x _6684 _6685 _6686)). Qed.
Lemma lem301399 {A : Type'} (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term1042 A n' f P R a) (h2 : term316 A a y P R n') : term1068 A n' f P R a.
Proof. exact (conj (@lem301265 A a y P R n' h2) (@lem301273 A n' f P R a h1)). Qed.
Lemma lem301401 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1067 A f _6688 n x _6684 _6685 _6686.
Proof. exact (EQ_MP (@lem301397 A f _6688 n x _6684 _6685 _6686) (@lem301378 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem301402 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1067 A f _6688 n x _6684 _6685 _6686.
Proof. exact (@lem301401 A _6688 _6684 _6685 _6686 n x f h1). Qed.
Lemma lem301403 {A : Type'} (n' : type977 A) (P : type1597 A) (R : type1594 A) (a : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1069 A n' f n x P R a.
Proof. exact (@lem301402 A (term1070 A n' f P R a) P R a n x f h1). Qed.
Lemma lem301406 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term779 A n x P R a.
Proof. exact (@lem301403 A n' P R a n x f h1 (@lem301399 A f a y P R n' h2 h3)). Qed.
Lemma lem301407 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1071 A n x P R a.
Proof. exact (fun h0 : term1072 A n x P R a => @lem301406 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem301409 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301410 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1071 A n x P R a) = (term779 A n x P R a).
Proof. exact (@lem301409 (term779 A n x P R a)). Qed.
Lemma lem301411 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term779 A n x P R a.
Proof. exact (EQ_MP (@lem301410 A n x P R a) (@lem301407 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301417 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301418 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1028 A P y _6690 _6691) = (term1073 A y P _6690 _6691).
Proof. exact (@lem301417 (term855 A P y _6690 _6691) (term861 A P _6690 _6691)). Qed.
Lemma lem301424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem301425 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1074 A P y _6690 _6691) = (term1075 A y P _6690 _6691).
Proof. exact (MK_COMB (@lem301424) (@lem301418 A y P _6690 _6691)). Qed.
Lemma lem301431 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1073 A y P _6690 _6691) = (term1073 A y P _6690 _6691).
Proof. exact (eq_refl (term1073 A y P _6690 _6691)). Qed.
Lemma lem301432 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : ((term1028 A P y _6690 _6691) = (term1073 A y P _6690 _6691)) = ((term1073 A y P _6690 _6691) = (term1073 A y P _6690 _6691)).
Proof. exact (MK_COMB (@lem301425 A y P _6690 _6691) (@lem301431 A y P _6690 _6691)). Qed.
Lemma lem301434 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem301435 (x : Prop) : (x = x) = True.
Proof. exact (@lem301434 Prop x). Qed.
Lemma lem301436 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : ((term1073 A y P _6690 _6691) = (term1073 A y P _6690 _6691)) = True.
Proof. exact (@lem301435 (term1073 A y P _6690 _6691)). Qed.
Lemma lem301437 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : ((term1028 A P y _6690 _6691) = (term1073 A y P _6690 _6691)) = True.
Proof. exact (TRANS (@lem301432 A y P _6690 _6691) (@lem301436 A y P _6690 _6691)). Qed.
Lemma lem301438 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : True = ((term1028 A P y _6690 _6691) = (term1073 A y P _6690 _6691)).
Proof. exact (SYM (@lem301437 A y P _6690 _6691)). Qed.
Lemma lem301439 {A : Type'} (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1028 A P y _6690 _6691) = (term1073 A y P _6690 _6691).
Proof. exact (EQ_MP (@lem301438 A y P _6690 _6691) (@lem0)). Qed.
Lemma lem301440 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1073 A y P _6690 _6691.
Proof. exact (EQ_MP (@lem301439 A y P _6690 _6691) (@lem300851 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem301442 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem301443 {A : Type'} (P : type1597 A) (y : type1596 A) (_6690 : nat) (_6691 : A) : (term1073 A y P _6690 _6691) = (term1076 A P y _6690 _6691).
Proof. exact (@lem301442 (term861 A P _6690 _6691) (term855 A P y _6690 _6691)). Qed.
Lemma lem301445 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem301446 {A : Type'} (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1077 A P _6690 _6691) = (term860 A P _6690 _6691).
Proof. exact (@lem301445 (term860 A P _6690 _6691)). Qed.
Lemma lem301447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem301448 {A : Type'} (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1078 A P _6690 _6691) = (term1079 A P _6690 _6691).
Proof. exact (MK_COMB (@lem301447) (@lem301446 A P _6690 _6691)). Qed.
Lemma lem301449 {A : Type'} (P : type1597 A) (y : type1596 A) (_6690 : nat) (_6691 : A) : (term855 A P y _6690 _6691) = (term855 A P y _6690 _6691).
Proof. exact (eq_refl (term855 A P y _6690 _6691)). Qed.
Lemma lem301450 {A : Type'} (P : type1597 A) (y : type1596 A) (_6690 : nat) (_6691 : A) : (term1076 A P y _6690 _6691) = (term1080 A P y _6690 _6691).
Proof. exact (MK_COMB (@lem301448 A P _6690 _6691) (@lem301449 A P y _6690 _6691)). Qed.
Lemma lem301451 {A : Type'} (P : type1597 A) (y : type1596 A) (_6690 : nat) (_6691 : A) : (term1073 A y P _6690 _6691) = (term1080 A P y _6690 _6691).
Proof. exact (TRANS (@lem301443 A P y _6690 _6691) (@lem301450 A P y _6690 _6691)). Qed.
Lemma lem301454 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1080 A P y _6690 _6691.
Proof. exact (EQ_MP (@lem301451 A P y _6690 _6691) (@lem301440 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem301455 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1080 A P y _6690 _6691.
Proof. exact (@lem301454 A _6690 _6691 a y P R n' h1). Qed.
Lemma lem301456 {A : Type'} (n : type946 A) (x : type945 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1081 A y n x P R a.
Proof. exact (@lem301455 A (term736 A n P R a) (term739 A x P R a) a y P R n' h1). Qed.
Lemma lem301459 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1082 A y n x P R a.
Proof. exact (@lem301456 A n x a y P R n' h3 (@lem301411 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301460 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1083 A y n x P R a.
Proof. exact (fun h0 : term1084 A y n x P R a => @lem301459 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem301462 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301463 {A : Type'} (y : type1596 A) (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1083 A y n x P R a) = (term1082 A y n x P R a).
Proof. exact (@lem301462 (term1082 A y n x P R a)). Qed.
Lemma lem301464 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1082 A y n x P R a.
Proof. exact (EQ_MP (@lem301463 A y n x P R a) (@lem301460 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301467 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1042 A n' f P R a) : term1042 A n' f P R a.
Proof. exact (h1). Qed.
Lemma lem301468 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1042 A n' f P R a) : term1043 A n' f P R a.
Proof. exact (fun h0 : term1044 A n' f P R a => @lem301467 A n' f P R a h1). Qed.
Lemma lem301470 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem301471 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1043 A n' f P R a) = (term1042 A n' f P R a).
Proof. exact (@lem301470 (term1044 A n' f P R a)). Qed.
Lemma lem301472 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1042 A n' f P R a) : term1042 A n' f P R a.
Proof. exact (EQ_MP (@lem301471 A n' f P R a) (@lem301468 A n' f P R a h1)). Qed.
Lemma lem301488 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301489 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1038 A n x _6687 f _6684 _6685 _6686 _6688) = (term1085 A x n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem301488 (term752 A n x _6684 _6685 _6686 _6687) (term764 A n _6684 _6685 _6686 _6687) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301503 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301504 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1086 A n _6687 f _6684 _6685 _6686 _6688) = (term1087 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (@lem301503 (term715 A f _6684 _6685 _6686 _6688) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301510 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1088 A n x _6684 _6685 _6686 _6687) = (term1088 A n x _6684 _6685 _6686 _6687).
Proof. exact (eq_refl (term1088 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem301511 {A : Type'} (x : type945 A) (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1085 A x n _6687 f _6684 _6685 _6686 _6688) = (term1089 A x f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301510 A n x _6684 _6685 _6686 _6687) (@lem301504 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301515 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301516 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1089 A x f _6688 n _6684 _6685 _6686 _6687) = (term1090 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (@lem301515 (term715 A f _6684 _6685 _6686 _6688) (term752 A n x _6684 _6685 _6686 _6687) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301532 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1085 A x n _6687 f _6684 _6685 _6686 _6688) = (term1090 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301511 A x f _6688 n _6684 _6685 _6686 _6687) (@lem301516 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301533 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1038 A n x _6687 f _6684 _6685 _6686 _6688) = (term1090 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301489 A x n _6687 f _6684 _6685 _6686 _6688) (@lem301532 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301534 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term791 A _6684 _6686) = (term791 A _6684 _6686).
Proof. exact (eq_refl (term791 A _6684 _6686)). Qed.
Lemma lem301535 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1039 A n x _6687 f _6684 _6685 _6686 _6688) = (term1091 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301534 A _6684 _6686) (@lem301533 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301539 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301540 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1091 A f _6688 x n _6684 _6685 _6686 _6687) = (term1092 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (@lem301539 (term715 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686) (term1093 A x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301554 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301555 {A : Type'} (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1094 A x n _6684 _6685 _6686 _6687) = (term1095 A x n _6684 _6685 _6686 _6687).
Proof. exact (@lem301554 (term752 A n x _6684 _6685 _6686 _6687) (term790 A _6684 _6686) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301571 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1096 A f _6684 _6685 _6686 _6688) = (term1096 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1096 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301572 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1092 A f _6688 x n _6684 _6685 _6686 _6687) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301571 A f _6684 _6685 _6686 _6688) (@lem301555 A x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301583 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1091 A f _6688 x n _6684 _6685 _6686 _6687) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301540 A f _6688 x n _6684 _6685 _6686 _6687) (@lem301572 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301584 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1039 A n x _6687 f _6684 _6685 _6686 _6688) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301535 A f _6688 x n _6684 _6685 _6686 _6687) (@lem301583 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem301586 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1098 A n x _6687 f _6684 _6685 _6686 _6688) = (term1099 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301585) (@lem301584 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301610 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301611 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1086 A n _6687 f _6684 _6685 _6686 _6688) = (term1087 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (@lem301610 (term715 A f _6684 _6685 _6686 _6688) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301617 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term791 A _6684 _6686) = (term791 A _6684 _6686).
Proof. exact (eq_refl (term791 A _6684 _6686)). Qed.
Lemma lem301618 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1100 A n _6687 f _6684 _6685 _6686 _6688) = (term1101 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301617 A _6684 _6686) (@lem301611 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301622 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301623 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1101 A f _6688 n _6684 _6685 _6686 _6687) = (term1102 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (@lem301622 (term715 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301639 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1100 A n _6687 f _6684 _6685 _6686 _6688) = (term1102 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301618 A f _6688 n _6684 _6685 _6686 _6687) (@lem301623 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301640 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1088 A n x _6684 _6685 _6686 _6687) = (term1088 A n x _6684 _6685 _6686 _6687).
Proof. exact (eq_refl (term1088 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem301641 {A : Type'} (x : type945 A) (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1103 A x n _6687 f _6684 _6685 _6686 _6688) = (term1104 A x f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301640 A n x _6684 _6685 _6686 _6687) (@lem301639 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301645 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301646 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1104 A x f _6688 n _6684 _6685 _6686 _6687) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (@lem301645 (term715 A f _6684 _6685 _6686 _6688) (term752 A n x _6684 _6685 _6686 _6687) (term1105 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301672 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1103 A x n _6687 f _6684 _6685 _6686 _6688) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301641 A x f _6688 n _6684 _6685 _6686 _6687) (@lem301646 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301673 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : ((term1039 A n x _6687 f _6684 _6685 _6686 _6688) = (term1103 A x n _6687 f _6684 _6685 _6686 _6688)) = ((term1097 A f _6688 x n _6684 _6685 _6686 _6687) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687)).
Proof. exact (MK_COMB (@lem301586 A f _6688 x n _6684 _6685 _6686 _6687) (@lem301672 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem301676 (x : Prop) : (x = x) = True.
Proof. exact (@lem301675 Prop x). Qed.
Lemma lem301677 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : ((term1097 A f _6688 x n _6684 _6685 _6686 _6687) = (term1097 A f _6688 x n _6684 _6685 _6686 _6687)) = True.
Proof. exact (@lem301676 (term1097 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301678 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : ((term1039 A n x _6687 f _6684 _6685 _6686 _6688) = (term1103 A x n _6687 f _6684 _6685 _6686 _6688)) = True.
Proof. exact (TRANS (@lem301673 A f _6688 x n _6684 _6685 _6686 _6687) (@lem301677 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301679 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : True = ((term1039 A n x _6687 f _6684 _6685 _6686 _6688) = (term1103 A x n _6687 f _6684 _6685 _6686 _6688)).
Proof. exact (SYM (@lem301678 A x n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301680 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1039 A n x _6687 f _6684 _6685 _6686 _6688) = (term1103 A x n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (EQ_MP (@lem301679 A x n _6687 f _6684 _6685 _6686 _6688) (@lem0)). Qed.
Lemma lem301681 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1103 A x n _6687 f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem301680 A x n _6687 f _6684 _6685 _6686 _6688) (@lem300917 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem301683 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem301684 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1103 A x n _6687 f _6684 _6685 _6686 _6688) = (term1106 A f _6688 n x _6684 _6685 _6686 _6687).
Proof. exact (@lem301683 (term1100 A n _6687 f _6684 _6685 _6686 _6688) (term752 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem301686 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem301687 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1107 A n _6687 f _6684 _6685 _6686 _6688) = (term1108 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem301686 (term790 A _6684 _6686) (term1086 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301689 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem301690 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1061 A _6684 _6686) = (term789 A _6684 _6686).
Proof. exact (@lem301689 (term789 A _6684 _6686)). Qed.
Lemma lem301691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem301692 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1062 A _6684 _6686) = (term870 A _6684 _6686).
Proof. exact (MK_COMB (@lem301691) (@lem301690 A _6684 _6686)). Qed.
Lemma lem301694 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem301695 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1109 A n _6687 f _6684 _6685 _6686 _6688) = (term1110 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem301694 (term764 A n _6684 _6685 _6686 _6687) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301697 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem301698 {A : Type'} (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1111 A n _6684 _6685 _6686 _6687) = (term762 A n _6684 _6685 _6686 _6687).
Proof. exact (@lem301697 (term762 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem301700 {A : Type'} (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1112 A n _6684 _6685 _6686 _6687) = (term1113 A n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301699) (@lem301698 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem301701 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1063 A f _6684 _6685 _6686 _6688) = (term1063 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1063 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301702 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1110 A n _6687 f _6684 _6685 _6686 _6688) = (term1114 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem301700 A n _6684 _6685 _6686 _6687) (@lem301701 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301703 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1109 A n _6687 f _6684 _6685 _6686 _6688) = (term1114 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem301695 A n _6687 f _6684 _6685 _6686 _6688) (@lem301702 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301704 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1108 A n _6687 f _6684 _6685 _6686 _6688) = (term1115 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem301692 A _6684 _6686) (@lem301703 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301705 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1107 A n _6687 f _6684 _6685 _6686 _6688) = (term1115 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem301687 A n _6687 f _6684 _6685 _6686 _6688) (@lem301704 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301706 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem301707 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1116 A n _6687 f _6684 _6685 _6686 _6688) = (term1117 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem301706) (@lem301705 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301708 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term752 A n x _6684 _6685 _6686 _6687) = (term752 A n x _6684 _6685 _6686 _6687).
Proof. exact (eq_refl (term752 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem301709 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1106 A f _6688 n x _6684 _6685 _6686 _6687) = (term1118 A f _6688 n x _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem301707 A n _6687 f _6684 _6685 _6686 _6688) (@lem301708 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem301710 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1103 A x n _6687 f _6684 _6685 _6686 _6688) = (term1118 A f _6688 n x _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem301684 A f _6688 n x _6684 _6685 _6686 _6687) (@lem301709 A f _6688 n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem301712 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1119 A y n x n' f P R a.
Proof. exact (conj (@lem301464 A n x f a y P R n' h1 h2 h3) (@lem301472 A n' f P R a h2)). Qed.
Lemma lem301713 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1120 A y n x n' f P R a.
Proof. exact (conj (@lem301258 A a y P R n' h3) (@lem301712 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301715 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1118 A f _6688 n x _6684 _6685 _6686 _6687.
Proof. exact (EQ_MP (@lem301710 A f _6688 n x _6684 _6685 _6686 _6687) (@lem301681 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem301716 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1118 A f _6688 n x _6684 _6685 _6686 _6687.
Proof. exact (@lem301715 A _6688 _6684 _6685 _6686 _6687 n x f h1). Qed.
Lemma lem301717 {A : Type'} (n' : type977 A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (a : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1121 A n' f y n x P R a.
Proof. exact (@lem301716 A (term1070 A n' f P R a) P R a (term1122 A y n x P R a) n x f h1). Qed.
Lemma lem301720 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1123 A y n x P R a.
Proof. exact (@lem301717 A n' y P R a n x f h1 (@lem301713 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301721 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1124 A y n x P R a.
Proof. exact (fun h0 : term1125 A y n x P R a => @lem301720 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem301723 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem301724 {A : Type'} (y : type1596 A) (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1124 A y n x P R a) = (term1123 A y n x P R a).
Proof. exact (@lem301723 (term1125 A y n x P R a)). Qed.
Lemma lem301725 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1123 A y n x P R a.
Proof. exact (EQ_MP (@lem301724 A y n x P R a) (@lem301721 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301727 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem301730 {A : Type'} (R : type1594 A) (y : type1596 A) (P : type1597 A) (_6690 : nat) (_6691 : A) : (term1029 A P R y _6690 _6691) = (term1126 A R y P _6690 _6691).
Proof. exact (@lem301727 (term848 A R y _6690 _6691) (term861 A P _6690 _6691)). Qed.
Lemma lem301733 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1126 A R y P _6690 _6691.
Proof. exact (EQ_MP (@lem301730 A R y P _6690 _6691) (@lem300857 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem301734 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1126 A R y P _6690 _6691.
Proof. exact (@lem301733 A _6690 _6691 a y P R n' h1). Qed.
Lemma lem301735 {A : Type'} (n : type946 A) (x : type945 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1127 A y n x P R a.
Proof. exact (@lem301734 A (term736 A n P R a) (term739 A x P R a) a y P R n' h1). Qed.
Lemma lem301738 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1072 A n x P R a.
Proof. exact (@lem301735 A n x a y P R n' h3 (@lem301725 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301739 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1128 A n x P R a.
Proof. exact (fun h0 : term779 A n x P R a => @lem301738 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem301741 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem301742 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1128 A n x P R a) = (term1072 A n x P R a).
Proof. exact (@lem301741 (term779 A n x P R a)). Qed.
Lemma lem301743 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1072 A n x P R a.
Proof. exact (EQ_MP (@lem301742 A n x P R a) (@lem301739 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301749 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301750 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1035 A n x f _6684 _6685 _6686 _6688) = (term1046 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem301749 (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301764 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301765 {A : Type'} (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1047 A f _6684 _6685 _6686 _6688) = (term1048 A f _6685 _6688 _6684 _6686).
Proof. exact (@lem301764 (term715 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686)). Qed.
Lemma lem301771 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1049 A n x _6684 _6685 _6686) = (term1049 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1049 A n x _6684 _6685 _6686)). Qed.
Lemma lem301772 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1050 A n x f _6685 _6688 _6684 _6686).
Proof. exact (MK_COMB (@lem301771 A n x _6684 _6685 _6686) (@lem301765 A f _6685 _6688 _6684 _6686)). Qed.
Lemma lem301776 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301777 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1050 A n x f _6685 _6688 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (@lem301776 (term715 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem301793 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1046 A n x f _6684 _6685 _6686 _6688) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301772 A n x f _6685 _6688 _6684 _6686) (@lem301777 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301794 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1035 A n x f _6684 _6685 _6686 _6688) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301750 A n x f _6684 _6685 _6686 _6688) (@lem301793 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem301796 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1052 A n x f _6684 _6685 _6686 _6688) = (term1053 A f _6688 n x _6685 _6684 _6686).
Proof. exact (MK_COMB (@lem301795) (@lem301794 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301810 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301811 {A : Type'} (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term989 A n x _6684 _6685 _6686) = (term1129 A n x _6685 _6684 _6686).
Proof. exact (@lem301810 (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem301817 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1096 A f _6684 _6685 _6686 _6688) = (term1096 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1096 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301818 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1130 A f _6688 n x _6684 _6685 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686).
Proof. exact (MK_COMB (@lem301817 A f _6684 _6685 _6686 _6688) (@lem301811 A n x _6685 _6684 _6686)). Qed.
Lemma lem301829 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1035 A n x f _6684 _6685 _6686 _6688) = (term1130 A f _6688 n x _6684 _6685 _6686)) = ((term1051 A f _6688 n x _6685 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686)).
Proof. exact (MK_COMB (@lem301796 A f _6688 n x _6685 _6684 _6686) (@lem301818 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301831 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem301832 (x : Prop) : (x = x) = True.
Proof. exact (@lem301831 Prop x). Qed.
Lemma lem301833 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1051 A f _6688 n x _6685 _6684 _6686) = (term1051 A f _6688 n x _6685 _6684 _6686)) = True.
Proof. exact (@lem301832 (term1051 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301834 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : ((term1035 A n x f _6684 _6685 _6686 _6688) = (term1130 A f _6688 n x _6684 _6685 _6686)) = True.
Proof. exact (TRANS (@lem301829 A f _6688 n x _6685 _6684 _6686) (@lem301833 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301835 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : True = ((term1035 A n x f _6684 _6685 _6686 _6688) = (term1130 A f _6688 n x _6684 _6685 _6686)).
Proof. exact (SYM (@lem301834 A f _6688 n x _6684 _6685 _6686)). Qed.
Lemma lem301836 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1035 A n x f _6684 _6685 _6686 _6688) = (term1130 A f _6688 n x _6684 _6685 _6686).
Proof. exact (EQ_MP (@lem301835 A f _6688 n x _6684 _6685 _6686) (@lem0)). Qed.
Lemma lem301837 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1130 A f _6688 n x _6684 _6685 _6686.
Proof. exact (EQ_MP (@lem301836 A f _6688 n x _6684 _6685 _6686) (@lem300899 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem301839 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem301840 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1130 A f _6688 n x _6684 _6685 _6686) = (term1131 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem301839 (term989 A n x _6684 _6685 _6686) (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301842 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem301843 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1132 A n x _6684 _6685 _6686) = (term1133 A n x _6684 _6685 _6686).
Proof. exact (@lem301842 (term790 A _6684 _6686) (term779 A n x _6684 _6685 _6686)). Qed.
Lemma lem301845 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem301846 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1061 A _6684 _6686) = (term789 A _6684 _6686).
Proof. exact (@lem301845 (term789 A _6684 _6686)). Qed.
Lemma lem301847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem301848 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1062 A _6684 _6686) = (term870 A _6684 _6686).
Proof. exact (MK_COMB (@lem301847) (@lem301846 A _6684 _6686)). Qed.
Lemma lem301849 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1072 A n x _6684 _6685 _6686) = (term1072 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1072 A n x _6684 _6685 _6686)). Qed.
Lemma lem301850 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1133 A n x _6684 _6685 _6686) = (term1134 A n x _6684 _6685 _6686).
Proof. exact (MK_COMB (@lem301848 A _6684 _6686) (@lem301849 A n x _6684 _6685 _6686)). Qed.
Lemma lem301851 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1132 A n x _6684 _6685 _6686) = (term1134 A n x _6684 _6685 _6686).
Proof. exact (TRANS (@lem301843 A n x _6684 _6685 _6686) (@lem301850 A n x _6684 _6685 _6686)). Qed.
Lemma lem301852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem301853 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1135 A n x _6684 _6685 _6686) = (term1136 A n x _6684 _6685 _6686).
Proof. exact (MK_COMB (@lem301852) (@lem301851 A n x _6684 _6685 _6686)). Qed.
Lemma lem301854 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term715 A f _6684 _6685 _6686 _6688) = (term715 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term715 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301855 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1131 A n x f _6684 _6685 _6686 _6688) = (term1137 A n x f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem301853 A n x _6684 _6685 _6686) (@lem301854 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301856 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1130 A f _6688 n x _6684 _6685 _6686) = (term1137 A n x f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem301840 A n x f _6684 _6685 _6686 _6688) (@lem301855 A n x f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301858 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1134 A n x P R a.
Proof. exact (conj (@lem301251 A a y P R n' h3) (@lem301743 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301860 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1137 A n x f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem301856 A n x f _6684 _6685 _6686 _6688) (@lem301837 A _6688 _6684 _6685 _6686 n x f h1)). Qed.
Lemma lem301861 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1137 A n x f _6684 _6685 _6686 _6688.
Proof. exact (@lem301860 A _6684 _6685 _6686 _6688 n x f h1). Qed.
Lemma lem301862 {A : Type'} (P : type1597 A) (R : type1594 A) (a : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1137 A n x f P R a _6688.
Proof. exact (@lem301861 A P R a _6688 n x f h1). Qed.
Lemma lem301865 {A : Type'} (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term715 A f P R a _6688.
Proof. exact (@lem301862 A P R a _6688 n x f h1 (@lem301858 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem301866 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1042 A n' f P R a) (h3 : term316 A a y P R n') : term1044 A n' f P R a.
Proof. exact (@lem301865 A (term1070 A n' f P R a) n x f a y P R n' h1 h2 h3). Qed.
Lemma lem301867 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : term1138 A n' f P R a.
Proof. exact (fun h0 : term1042 A n' f P R a => @lem301866 A n x f a y P R n' h1 h0 h2). Qed.
Lemma lem301869 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301870 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1138 A n' f P R a) = (term1044 A n' f P R a).
Proof. exact (@lem301869 (term1044 A n' f P R a)). Qed.
Lemma lem301871 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : term1044 A n' f P R a.
Proof. exact (EQ_MP (@lem301870 A n' f P R a) (@lem301867 A n x f a y P R n' h1 h2)). Qed.
Lemma lem301873 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (proj1 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem301874 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1040 A P a.
Proof. exact (fun h0 : term790 A P a => @lem301873 A a y P R n' h1). Qed.
Lemma lem301876 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301877 {A : Type'} (P : type1597 A) (a : A) : (term1040 A P a) = (term789 A P a).
Proof. exact (@lem301876 (term789 A P a)). Qed.
Lemma lem301878 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (EQ_MP (@lem301877 A P a) (@lem301874 A a y P R n' h1)). Qed.
Lemma lem301880 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (proj1 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem301881 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1040 A P a.
Proof. exact (fun h0 : term790 A P a => @lem301880 A a y P R n' h1). Qed.
Lemma lem301883 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301884 {A : Type'} (P : type1597 A) (a : A) : (term1040 A P a) = (term789 A P a).
Proof. exact (@lem301883 (term789 A P a)). Qed.
Lemma lem301885 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (EQ_MP (@lem301884 A P a) (@lem301881 A a y P R n' h1)). Qed.
Lemma lem301887 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (proj1 (@lem300518 A a y P R n' h1)). Qed.
Lemma lem301888 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1040 A P a.
Proof. exact (fun h0 : term790 A P a => @lem301887 A a y P R n' h1). Qed.
Lemma lem301890 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem301891 {A : Type'} (P : type1597 A) (a : A) : (term1040 A P a) = (term789 A P a).
Proof. exact (@lem301890 (term789 A P a)). Qed.
Lemma lem301892 {A : Type'} (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term789 A P a.
Proof. exact (EQ_MP (@lem301891 A P a) (@lem301888 A a y P R n' h1)). Qed.
Lemma lem301895 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1139 A n' f P R a) : term1139 A n' f P R a.
Proof. exact (h1). Qed.
Lemma lem301896 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1139 A n' f P R a) : term1140 A n' f P R a.
Proof. exact (fun h0 : term1141 A n' f P R a => @lem301895 A n' f P R a h1). Qed.
Lemma lem301898 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem301899 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1140 A n' f P R a) = (term1139 A n' f P R a).
Proof. exact (@lem301898 (term1141 A n' f P R a)). Qed.
Lemma lem301900 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1139 A n' f P R a) : term1139 A n' f P R a.
Proof. exact (EQ_MP (@lem301899 A n' f P R a) (@lem301896 A n' f P R a h1)). Qed.
Lemma lem301906 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301907 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1030 A n x f _6684 _6685 _6686 _6688) = (term1142 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem301906 (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem301921 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301922 {A : Type'} (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1143 A f _6684 _6685 _6686 _6688) = (term1144 A f _6685 _6688 _6684 _6686).
Proof. exact (@lem301921 (term707 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686)). Qed.
Lemma lem301928 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1049 A n x _6684 _6685 _6686) = (term1049 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1049 A n x _6684 _6685 _6686)). Qed.
Lemma lem301929 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1145 A n x f _6685 _6688 _6684 _6686).
Proof. exact (MK_COMB (@lem301928 A n x _6684 _6685 _6686) (@lem301922 A f _6685 _6688 _6684 _6686)). Qed.
Lemma lem301933 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301934 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1145 A n x f _6685 _6688 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (@lem301933 (term707 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem301950 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301929 A n x f _6685 _6688 _6684 _6686) (@lem301934 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301951 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1030 A n x f _6684 _6685 _6686 _6688) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301907 A n x f _6684 _6685 _6686 _6688) (@lem301950 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem301953 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1147 A n x f _6684 _6685 _6686 _6688) = (term1148 A f _6688 n x _6685 _6684 _6686).
Proof. exact (MK_COMB (@lem301952) (@lem301951 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301967 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem301968 {A : Type'} (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1143 A f _6684 _6685 _6686 _6688) = (term1144 A f _6685 _6688 _6684 _6686).
Proof. exact (@lem301967 (term707 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686)). Qed.
Lemma lem301974 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1049 A n x _6684 _6685 _6686) = (term1049 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1049 A n x _6684 _6685 _6686)). Qed.
Lemma lem301975 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1145 A n x f _6685 _6688 _6684 _6686).
Proof. exact (MK_COMB (@lem301974 A n x _6684 _6685 _6686) (@lem301968 A f _6685 _6688 _6684 _6686)). Qed.
Lemma lem301979 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem301980 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1145 A n x f _6685 _6688 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (@lem301979 (term707 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem301996 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem301975 A n x f _6685 _6688 _6684 _6686) (@lem301980 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301997 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1030 A n x f _6684 _6685 _6686 _6688) = (term1142 A n x f _6684 _6685 _6686 _6688)) = ((term1146 A f _6688 n x _6685 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686)).
Proof. exact (MK_COMB (@lem301953 A f _6688 n x _6685 _6684 _6686) (@lem301996 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem301999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem302000 (x : Prop) : (x = x) = True.
Proof. exact (@lem301999 Prop x). Qed.
Lemma lem302001 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1146 A f _6688 n x _6685 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686)) = True.
Proof. exact (@lem302000 (term1146 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302002 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : ((term1030 A n x f _6684 _6685 _6686 _6688) = (term1142 A n x f _6684 _6685 _6686 _6688)) = True.
Proof. exact (TRANS (@lem301997 A f _6688 n x _6685 _6684 _6686) (@lem302001 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302003 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : True = ((term1030 A n x f _6684 _6685 _6686 _6688) = (term1142 A n x f _6684 _6685 _6686 _6688)).
Proof. exact (SYM (@lem302002 A n x f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302004 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1030 A n x f _6684 _6685 _6686 _6688) = (term1142 A n x f _6684 _6685 _6686 _6688).
Proof. exact (EQ_MP (@lem302003 A n x f _6684 _6685 _6686 _6688) (@lem0)). Qed.
Lemma lem302005 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1142 A n x f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem302004 A n x f _6684 _6685 _6686 _6688) (@lem300869 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem302007 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem302008 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1149 A f _6688 n x _6684 _6685 _6686).
Proof. exact (@lem302007 (term1143 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686)). Qed.
Lemma lem302010 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem302011 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1150 A f _6684 _6685 _6686 _6688) = (term1151 A f _6684 _6685 _6686 _6688).
Proof. exact (@lem302010 (term790 A _6684 _6686) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302013 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem302014 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1061 A _6684 _6686) = (term789 A _6684 _6686).
Proof. exact (@lem302013 (term789 A _6684 _6686)). Qed.
Lemma lem302015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem302016 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1062 A _6684 _6686) = (term870 A _6684 _6686).
Proof. exact (MK_COMB (@lem302015) (@lem302014 A _6684 _6686)). Qed.
Lemma lem302017 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1152 A f _6684 _6685 _6686 _6688) = (term1152 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1152 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302018 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1151 A f _6684 _6685 _6686 _6688) = (term1153 A f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem302016 A _6684 _6686) (@lem302017 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302019 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1150 A f _6684 _6685 _6686 _6688) = (term1153 A f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem302011 A f _6684 _6685 _6686 _6688) (@lem302018 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem302021 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1154 A f _6684 _6685 _6686 _6688) = (term1155 A f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem302020) (@lem302019 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302022 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term779 A n x _6684 _6685 _6686) = (term779 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term779 A n x _6684 _6685 _6686)). Qed.
Lemma lem302023 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1149 A f _6688 n x _6684 _6685 _6686) = (term1156 A f _6688 n x _6684 _6685 _6686).
Proof. exact (MK_COMB (@lem302021 A f _6684 _6685 _6686 _6688) (@lem302022 A n x _6684 _6685 _6686)). Qed.
Lemma lem302024 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1156 A f _6688 n x _6684 _6685 _6686).
Proof. exact (TRANS (@lem302008 A f _6688 n x _6684 _6685 _6686) (@lem302023 A f _6688 n x _6684 _6685 _6686)). Qed.
Lemma lem302026 {A : Type'} (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term1139 A n' f P R a) (h2 : term316 A a y P R n') : term1157 A n' f P R a.
Proof. exact (conj (@lem301892 A a y P R n' h2) (@lem301900 A n' f P R a h1)). Qed.
Lemma lem302028 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1156 A f _6688 n x _6684 _6685 _6686.
Proof. exact (EQ_MP (@lem302024 A f _6688 n x _6684 _6685 _6686) (@lem302005 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem302029 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1156 A f _6688 n x _6684 _6685 _6686.
Proof. exact (@lem302028 A _6688 _6684 _6685 _6686 n x f h1). Qed.
Lemma lem302030 {A : Type'} (n' : type977 A) (P : type1597 A) (R : type1594 A) (a : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1158 A n' f n x P R a.
Proof. exact (@lem302029 A (term1070 A n' f P R a) P R a n x f h1). Qed.
Lemma lem302033 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term779 A n x P R a.
Proof. exact (@lem302030 A n' P R a n x f h1 (@lem302026 A f a y P R n' h2 h3)). Qed.
Lemma lem302034 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1071 A n x P R a.
Proof. exact (fun h0 : term1072 A n x P R a => @lem302033 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem302036 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem302037 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1071 A n x P R a) = (term779 A n x P R a).
Proof. exact (@lem302036 (term779 A n x P R a)). Qed.
Lemma lem302038 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term779 A n x P R a.
Proof. exact (EQ_MP (@lem302037 A n x P R a) (@lem302034 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302040 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1080 A P y _6690 _6691.
Proof. exact (EQ_MP (@lem301451 A P y _6690 _6691) (@lem301440 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem302041 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1080 A P y _6690 _6691.
Proof. exact (@lem302040 A _6690 _6691 a y P R n' h1). Qed.
Lemma lem302042 {A : Type'} (n : type946 A) (x : type945 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1081 A y n x P R a.
Proof. exact (@lem302041 A (term736 A n P R a) (term739 A x P R a) a y P R n' h1). Qed.
Lemma lem302045 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1082 A y n x P R a.
Proof. exact (@lem302042 A n x a y P R n' h3 (@lem302038 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302046 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1083 A y n x P R a.
Proof. exact (fun h0 : term1084 A y n x P R a => @lem302045 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem302048 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem302049 {A : Type'} (y : type1596 A) (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1083 A y n x P R a) = (term1082 A y n x P R a).
Proof. exact (@lem302048 (term1082 A y n x P R a)). Qed.
Lemma lem302050 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1082 A y n x P R a.
Proof. exact (EQ_MP (@lem302049 A y n x P R a) (@lem302046 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302053 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1139 A n' f P R a) : term1139 A n' f P R a.
Proof. exact (h1). Qed.
Lemma lem302054 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1139 A n' f P R a) : term1140 A n' f P R a.
Proof. exact (fun h0 : term1141 A n' f P R a => @lem302053 A n' f P R a h1). Qed.
Lemma lem302056 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem302057 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1140 A n' f P R a) = (term1139 A n' f P R a).
Proof. exact (@lem302056 (term1141 A n' f P R a)). Qed.
Lemma lem302058 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) (h1 : term1139 A n' f P R a) : term1139 A n' f P R a.
Proof. exact (EQ_MP (@lem302057 A n' f P R a) (@lem302054 A n' f P R a h1)). Qed.
Lemma lem302074 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302075 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1033 A n x _6687 f _6684 _6685 _6686 _6688) = (term1159 A x n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem302074 (term752 A n x _6684 _6685 _6686 _6687) (term764 A n _6684 _6685 _6686 _6687) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302089 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem302090 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1160 A n _6687 f _6684 _6685 _6686 _6688) = (term1161 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (@lem302089 (term707 A f _6684 _6685 _6686 _6688) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302096 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1088 A n x _6684 _6685 _6686 _6687) = (term1088 A n x _6684 _6685 _6686 _6687).
Proof. exact (eq_refl (term1088 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem302097 {A : Type'} (x : type945 A) (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1159 A x n _6687 f _6684 _6685 _6686 _6688) = (term1162 A x f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302096 A n x _6684 _6685 _6686 _6687) (@lem302090 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302101 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302102 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1162 A x f _6688 n _6684 _6685 _6686 _6687) = (term1163 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (@lem302101 (term707 A f _6684 _6685 _6686 _6688) (term752 A n x _6684 _6685 _6686 _6687) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302118 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1159 A x n _6687 f _6684 _6685 _6686 _6688) = (term1163 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302097 A x f _6688 n _6684 _6685 _6686 _6687) (@lem302102 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302119 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1033 A n x _6687 f _6684 _6685 _6686 _6688) = (term1163 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302075 A x n _6687 f _6684 _6685 _6686 _6688) (@lem302118 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302120 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term791 A _6684 _6686) = (term791 A _6684 _6686).
Proof. exact (eq_refl (term791 A _6684 _6686)). Qed.
Lemma lem302121 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1034 A n x _6687 f _6684 _6685 _6686 _6688) = (term1164 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302120 A _6684 _6686) (@lem302119 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302125 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302126 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1164 A f _6688 x n _6684 _6685 _6686 _6687) = (term1165 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (@lem302125 (term707 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686) (term1093 A x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302140 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302141 {A : Type'} (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1094 A x n _6684 _6685 _6686 _6687) = (term1095 A x n _6684 _6685 _6686 _6687).
Proof. exact (@lem302140 (term752 A n x _6684 _6685 _6686 _6687) (term790 A _6684 _6686) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302157 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1166 A f _6684 _6685 _6686 _6688) = (term1166 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1166 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302158 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1165 A f _6688 x n _6684 _6685 _6686 _6687) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302157 A f _6684 _6685 _6686 _6688) (@lem302141 A x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302169 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1164 A f _6688 x n _6684 _6685 _6686 _6687) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302126 A f _6688 x n _6684 _6685 _6686 _6687) (@lem302158 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302170 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1034 A n x _6687 f _6684 _6685 _6686 _6688) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302121 A f _6688 x n _6684 _6685 _6686 _6687) (@lem302169 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem302172 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1168 A n x _6687 f _6684 _6685 _6686 _6688) = (term1169 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302171) (@lem302170 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302196 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem302197 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1160 A n _6687 f _6684 _6685 _6686 _6688) = (term1161 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (@lem302196 (term707 A f _6684 _6685 _6686 _6688) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302203 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term791 A _6684 _6686) = (term791 A _6684 _6686).
Proof. exact (eq_refl (term791 A _6684 _6686)). Qed.
Lemma lem302204 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1170 A n _6687 f _6684 _6685 _6686 _6688) = (term1171 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302203 A _6684 _6686) (@lem302197 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302208 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302209 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1171 A f _6688 n _6684 _6685 _6686 _6687) = (term1172 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (@lem302208 (term707 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686) (term764 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302225 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1170 A n _6687 f _6684 _6685 _6686 _6688) = (term1172 A f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302204 A f _6688 n _6684 _6685 _6686 _6687) (@lem302209 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302226 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1088 A n x _6684 _6685 _6686 _6687) = (term1088 A n x _6684 _6685 _6686 _6687).
Proof. exact (eq_refl (term1088 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem302227 {A : Type'} (x : type945 A) (f : type944 A) (_6688 : nat) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1173 A x n _6687 f _6684 _6685 _6686 _6688) = (term1174 A x f _6688 n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302226 A n x _6684 _6685 _6686 _6687) (@lem302225 A f _6688 n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302232 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1174 A x f _6688 n _6684 _6685 _6686 _6687) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (@lem302231 (term707 A f _6684 _6685 _6686 _6688) (term752 A n x _6684 _6685 _6686 _6687) (term1105 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302258 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1173 A x n _6687 f _6684 _6685 _6686 _6688) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302227 A x f _6688 n _6684 _6685 _6686 _6687) (@lem302232 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302259 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : ((term1034 A n x _6687 f _6684 _6685 _6686 _6688) = (term1173 A x n _6687 f _6684 _6685 _6686 _6688)) = ((term1167 A f _6688 x n _6684 _6685 _6686 _6687) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687)).
Proof. exact (MK_COMB (@lem302172 A f _6688 x n _6684 _6685 _6686 _6687) (@lem302258 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem302262 (x : Prop) : (x = x) = True.
Proof. exact (@lem302261 Prop x). Qed.
Lemma lem302263 {A : Type'} (f : type944 A) (_6688 : nat) (x : type945 A) (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : ((term1167 A f _6688 x n _6684 _6685 _6686 _6687) = (term1167 A f _6688 x n _6684 _6685 _6686 _6687)) = True.
Proof. exact (@lem302262 (term1167 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302264 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : ((term1034 A n x _6687 f _6684 _6685 _6686 _6688) = (term1173 A x n _6687 f _6684 _6685 _6686 _6688)) = True.
Proof. exact (TRANS (@lem302259 A f _6688 x n _6684 _6685 _6686 _6687) (@lem302263 A f _6688 x n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302265 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : True = ((term1034 A n x _6687 f _6684 _6685 _6686 _6688) = (term1173 A x n _6687 f _6684 _6685 _6686 _6688)).
Proof. exact (SYM (@lem302264 A x n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302266 {A : Type'} (x : type945 A) (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1034 A n x _6687 f _6684 _6685 _6686 _6688) = (term1173 A x n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (EQ_MP (@lem302265 A x n _6687 f _6684 _6685 _6686 _6688) (@lem0)). Qed.
Lemma lem302267 {A : Type'} (_6687 : A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1173 A x n _6687 f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem302266 A x n _6687 f _6684 _6685 _6686 _6688) (@lem300887 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem302269 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem302270 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1173 A x n _6687 f _6684 _6685 _6686 _6688) = (term1175 A f _6688 n x _6684 _6685 _6686 _6687).
Proof. exact (@lem302269 (term1170 A n _6687 f _6684 _6685 _6686 _6688) (term752 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem302272 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem302273 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1176 A n _6687 f _6684 _6685 _6686 _6688) = (term1177 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem302272 (term790 A _6684 _6686) (term1160 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302275 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem302276 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1061 A _6684 _6686) = (term789 A _6684 _6686).
Proof. exact (@lem302275 (term789 A _6684 _6686)). Qed.
Lemma lem302277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem302278 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1062 A _6684 _6686) = (term870 A _6684 _6686).
Proof. exact (MK_COMB (@lem302277) (@lem302276 A _6684 _6686)). Qed.
Lemma lem302280 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem302281 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1178 A n _6687 f _6684 _6685 _6686 _6688) = (term1179 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (@lem302280 (term764 A n _6684 _6685 _6686 _6687) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302283 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem302284 {A : Type'} (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1111 A n _6684 _6685 _6686 _6687) = (term762 A n _6684 _6685 _6686 _6687).
Proof. exact (@lem302283 (term762 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem302286 {A : Type'} (n : type946 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1112 A n _6684 _6685 _6686 _6687) = (term1113 A n _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302285) (@lem302284 A n _6684 _6685 _6686 _6687)). Qed.
Lemma lem302287 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1152 A f _6684 _6685 _6686 _6688) = (term1152 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1152 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302288 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1179 A n _6687 f _6684 _6685 _6686 _6688) = (term1180 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem302286 A n _6684 _6685 _6686 _6687) (@lem302287 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302289 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1178 A n _6687 f _6684 _6685 _6686 _6688) = (term1180 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem302281 A n _6687 f _6684 _6685 _6686 _6688) (@lem302288 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302290 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1177 A n _6687 f _6684 _6685 _6686 _6688) = (term1181 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem302278 A _6684 _6686) (@lem302289 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302291 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1176 A n _6687 f _6684 _6685 _6686 _6688) = (term1181 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem302273 A n _6687 f _6684 _6685 _6686 _6688) (@lem302290 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem302293 {A : Type'} (n : type946 A) (_6687 : A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1182 A n _6687 f _6684 _6685 _6686 _6688) = (term1183 A n _6687 f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem302292) (@lem302291 A n _6687 f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302294 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term752 A n x _6684 _6685 _6686 _6687) = (term752 A n x _6684 _6685 _6686 _6687).
Proof. exact (eq_refl (term752 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem302295 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1175 A f _6688 n x _6684 _6685 _6686 _6687) = (term1184 A f _6688 n x _6684 _6685 _6686 _6687).
Proof. exact (MK_COMB (@lem302293 A n _6687 f _6684 _6685 _6686 _6688) (@lem302294 A n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem302296 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) : (term1173 A x n _6687 f _6684 _6685 _6686 _6688) = (term1184 A f _6688 n x _6684 _6685 _6686 _6687).
Proof. exact (TRANS (@lem302270 A f _6688 n x _6684 _6685 _6686 _6687) (@lem302295 A f _6688 n x _6684 _6685 _6686 _6687)). Qed.
Lemma lem302298 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1185 A y n x n' f P R a.
Proof. exact (conj (@lem302050 A n x f a y P R n' h1 h2 h3) (@lem302058 A n' f P R a h2)). Qed.
Lemma lem302299 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1186 A y n x n' f P R a.
Proof. exact (conj (@lem301885 A a y P R n' h3) (@lem302298 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302301 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1184 A f _6688 n x _6684 _6685 _6686 _6687.
Proof. exact (EQ_MP (@lem302296 A f _6688 n x _6684 _6685 _6686 _6687) (@lem302267 A _6687 _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem302302 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6687 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1184 A f _6688 n x _6684 _6685 _6686 _6687.
Proof. exact (@lem302301 A _6688 _6684 _6685 _6686 _6687 n x f h1). Qed.
Lemma lem302303 {A : Type'} (n' : type977 A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (a : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1187 A n' f y n x P R a.
Proof. exact (@lem302302 A (term1070 A n' f P R a) P R a (term1122 A y n x P R a) n x f h1). Qed.
Lemma lem302306 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1123 A y n x P R a.
Proof. exact (@lem302303 A n' y P R a n x f h1 (@lem302299 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302307 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1124 A y n x P R a.
Proof. exact (fun h0 : term1125 A y n x P R a => @lem302306 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem302309 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem302310 {A : Type'} (y : type1596 A) (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1124 A y n x P R a) = (term1123 A y n x P R a).
Proof. exact (@lem302309 (term1125 A y n x P R a)). Qed.
Lemma lem302311 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1123 A y n x P R a.
Proof. exact (EQ_MP (@lem302310 A y n x P R a) (@lem302307 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302313 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1126 A R y P _6690 _6691.
Proof. exact (EQ_MP (@lem301730 A R y P _6690 _6691) (@lem300857 A _6690 _6691 a y P R n' h1)). Qed.
Lemma lem302314 {A : Type'} (_6690 : nat) (_6691 : A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1126 A R y P _6690 _6691.
Proof. exact (@lem302313 A _6690 _6691 a y P R n' h1). Qed.
Lemma lem302315 {A : Type'} (n : type946 A) (x : type945 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1127 A y n x P R a.
Proof. exact (@lem302314 A (term736 A n P R a) (term739 A x P R a) a y P R n' h1). Qed.
Lemma lem302318 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1072 A n x P R a.
Proof. exact (@lem302315 A n x a y P R n' h3 (@lem302311 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302319 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1128 A n x P R a.
Proof. exact (fun h0 : term779 A n x P R a => @lem302318 A n x f a y P R n' h1 h2 h3). Qed.
Lemma lem302321 (p : Prop) : (term1045 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem302322 {A : Type'} (n : type946 A) (x : type945 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1128 A n x P R a) = (term1072 A n x P R a).
Proof. exact (@lem302321 (term779 A n x P R a)). Qed.
Lemma lem302323 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1072 A n x P R a.
Proof. exact (EQ_MP (@lem302322 A n x P R a) (@lem302319 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302329 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302330 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1030 A n x f _6684 _6685 _6686 _6688) = (term1142 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem302329 (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302344 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem302345 {A : Type'} (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1143 A f _6684 _6685 _6686 _6688) = (term1144 A f _6685 _6688 _6684 _6686).
Proof. exact (@lem302344 (term707 A f _6684 _6685 _6686 _6688) (term790 A _6684 _6686)). Qed.
Lemma lem302351 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1049 A n x _6684 _6685 _6686) = (term1049 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1049 A n x _6684 _6685 _6686)). Qed.
Lemma lem302352 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6685 : type1594 A) (_6688 : nat) (_6684 : type1597 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1145 A n x f _6685 _6688 _6684 _6686).
Proof. exact (MK_COMB (@lem302351 A n x _6684 _6685 _6686) (@lem302345 A f _6685 _6688 _6684 _6686)). Qed.
Lemma lem302356 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem302357 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1145 A n x f _6685 _6688 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (@lem302356 (term707 A f _6684 _6685 _6686 _6688) (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem302373 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1142 A n x f _6684 _6685 _6686 _6688) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem302352 A n x f _6685 _6688 _6684 _6686) (@lem302357 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302374 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1030 A n x f _6684 _6685 _6686 _6688) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (TRANS (@lem302330 A n x f _6684 _6685 _6686 _6688) (@lem302373 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem302376 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1147 A n x f _6684 _6685 _6686 _6688) = (term1148 A f _6688 n x _6685 _6684 _6686).
Proof. exact (MK_COMB (@lem302375) (@lem302374 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302390 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem302391 {A : Type'} (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term989 A n x _6684 _6685 _6686) = (term1129 A n x _6685 _6684 _6686).
Proof. exact (@lem302390 (term779 A n x _6684 _6685 _6686) (term790 A _6684 _6686)). Qed.
Lemma lem302397 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1166 A f _6684 _6685 _6686 _6688) = (term1166 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term1166 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302398 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : (term1188 A f _6688 n x _6684 _6685 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686).
Proof. exact (MK_COMB (@lem302397 A f _6684 _6685 _6686 _6688) (@lem302391 A n x _6685 _6684 _6686)). Qed.
Lemma lem302409 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1030 A n x f _6684 _6685 _6686 _6688) = (term1188 A f _6688 n x _6684 _6685 _6686)) = ((term1146 A f _6688 n x _6685 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686)).
Proof. exact (MK_COMB (@lem302376 A f _6688 n x _6685 _6684 _6686) (@lem302398 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem302412 (x : Prop) : (x = x) = True.
Proof. exact (@lem302411 Prop x). Qed.
Lemma lem302413 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6685 : type1594 A) (_6684 : type1597 A) (_6686 : A) : ((term1146 A f _6688 n x _6685 _6684 _6686) = (term1146 A f _6688 n x _6685 _6684 _6686)) = True.
Proof. exact (@lem302412 (term1146 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302414 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : ((term1030 A n x f _6684 _6685 _6686 _6688) = (term1188 A f _6688 n x _6684 _6685 _6686)) = True.
Proof. exact (TRANS (@lem302409 A f _6688 n x _6685 _6684 _6686) (@lem302413 A f _6688 n x _6685 _6684 _6686)). Qed.
Lemma lem302415 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : True = ((term1030 A n x f _6684 _6685 _6686 _6688) = (term1188 A f _6688 n x _6684 _6685 _6686)).
Proof. exact (SYM (@lem302414 A f _6688 n x _6684 _6685 _6686)). Qed.
Lemma lem302416 {A : Type'} (f : type944 A) (_6688 : nat) (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1030 A n x f _6684 _6685 _6686 _6688) = (term1188 A f _6688 n x _6684 _6685 _6686).
Proof. exact (EQ_MP (@lem302415 A f _6688 n x _6684 _6685 _6686) (@lem0)). Qed.
Lemma lem302417 {A : Type'} (_6688 : nat) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1188 A f _6688 n x _6684 _6685 _6686.
Proof. exact (EQ_MP (@lem302416 A f _6688 n x _6684 _6685 _6686) (@lem300869 A _6684 _6685 _6686 _6688 n x f h1)). Qed.
Lemma lem302419 (b : Prop) (a : Prop) : (a \/ b) = (term1054 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem302420 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1188 A f _6688 n x _6684 _6685 _6686) = (term1189 A n x f _6684 _6685 _6686 _6688).
Proof. exact (@lem302419 (term989 A n x _6684 _6685 _6686) (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302422 (a : Prop) (b : Prop) : (term1056 a b) = (term1057 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem302423 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1132 A n x _6684 _6685 _6686) = (term1133 A n x _6684 _6685 _6686).
Proof. exact (@lem302422 (term790 A _6684 _6686) (term779 A n x _6684 _6685 _6686)). Qed.
Lemma lem302425 (a : Prop) : (term1060 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem302426 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1061 A _6684 _6686) = (term789 A _6684 _6686).
Proof. exact (@lem302425 (term789 A _6684 _6686)). Qed.
Lemma lem302427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem302428 {A : Type'} (_6684 : type1597 A) (_6686 : A) : (term1062 A _6684 _6686) = (term870 A _6684 _6686).
Proof. exact (MK_COMB (@lem302427) (@lem302426 A _6684 _6686)). Qed.
Lemma lem302429 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1072 A n x _6684 _6685 _6686) = (term1072 A n x _6684 _6685 _6686).
Proof. exact (eq_refl (term1072 A n x _6684 _6685 _6686)). Qed.
Lemma lem302430 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1133 A n x _6684 _6685 _6686) = (term1134 A n x _6684 _6685 _6686).
Proof. exact (MK_COMB (@lem302428 A _6684 _6686) (@lem302429 A n x _6684 _6685 _6686)). Qed.
Lemma lem302431 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1132 A n x _6684 _6685 _6686) = (term1134 A n x _6684 _6685 _6686).
Proof. exact (TRANS (@lem302423 A n x _6684 _6685 _6686) (@lem302430 A n x _6684 _6685 _6686)). Qed.
Lemma lem302432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem302433 {A : Type'} (n : type946 A) (x : type945 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) : (term1135 A n x _6684 _6685 _6686) = (term1136 A n x _6684 _6685 _6686).
Proof. exact (MK_COMB (@lem302432) (@lem302431 A n x _6684 _6685 _6686)). Qed.
Lemma lem302434 {A : Type'} (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term707 A f _6684 _6685 _6686 _6688) = (term707 A f _6684 _6685 _6686 _6688).
Proof. exact (eq_refl (term707 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302435 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1189 A n x f _6684 _6685 _6686 _6688) = (term1190 A n x f _6684 _6685 _6686 _6688).
Proof. exact (MK_COMB (@lem302433 A n x _6684 _6685 _6686) (@lem302434 A f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302436 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) : (term1188 A f _6688 n x _6684 _6685 _6686) = (term1190 A n x f _6684 _6685 _6686 _6688).
Proof. exact (TRANS (@lem302420 A n x f _6684 _6685 _6686 _6688) (@lem302435 A n x f _6684 _6685 _6686 _6688)). Qed.
Lemma lem302438 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1134 A n x P R a.
Proof. exact (conj (@lem301878 A a y P R n' h3) (@lem302323 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302440 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1190 A n x f _6684 _6685 _6686 _6688.
Proof. exact (EQ_MP (@lem302436 A n x f _6684 _6685 _6686 _6688) (@lem302417 A _6688 _6684 _6685 _6686 n x f h1)). Qed.
Lemma lem302441 {A : Type'} (_6684 : type1597 A) (_6685 : type1594 A) (_6686 : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1190 A n x f _6684 _6685 _6686 _6688.
Proof. exact (@lem302440 A _6684 _6685 _6686 _6688 n x f h1). Qed.
Lemma lem302442 {A : Type'} (P : type1597 A) (R : type1594 A) (a : A) (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) : term1190 A n x f P R a _6688.
Proof. exact (@lem302441 A P R a _6688 n x f h1). Qed.
Lemma lem302445 {A : Type'} (_6688 : nat) (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term707 A f P R a _6688.
Proof. exact (@lem302442 A P R a _6688 n x f h1 (@lem302438 A n x f a y P R n' h1 h2 h3)). Qed.
Lemma lem302446 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term1139 A n' f P R a) (h3 : term316 A a y P R n') : term1141 A n' f P R a.
Proof. exact (@lem302445 A (term1070 A n' f P R a) n x f a y P R n' h1 h2 h3). Qed.
Lemma lem302447 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : term1191 A n' f P R a.
Proof. exact (fun h0 : term1139 A n' f P R a => @lem302446 A n x f a y P R n' h1 h0 h2). Qed.
Lemma lem302449 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem302450 {A : Type'} (n' : type977 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (a : A) : (term1191 A n' f P R a) = (term1141 A n' f P R a).
Proof. exact (@lem302449 (term1141 A n' f P R a)). Qed.
Lemma lem302451 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : term1141 A n' f P R a.
Proof. exact (EQ_MP (@lem302450 A n' f P R a) (@lem302447 A n x f a y P R n' h1 h2)). Qed.
Lemma lem302453 (a : Prop) (b : Prop) : (term1192 a b) = (term1193 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem302454 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) (_6689 : nat -> A) : (term840 A P R n' _6689) = (term1194 A P R n' _6689).
Proof. exact (@lem302453 (term835 A P n' _6689) (term826 A R n' _6689)). Qed.
Lemma lem302456 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem302457 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) (_6689 : nat -> A) : (term1194 A P R n' _6689) = (term1195 A P R n' _6689).
Proof. exact (@lem302456 (term1196 A P R n' _6689)). Qed.
Lemma lem302458 {A : Type'} (P : type1597 A) (R : type1594 A) (n' : type977 A) (_6689 : nat -> A) : (term840 A P R n' _6689) = (term1195 A P R n' _6689).
Proof. exact (TRANS (@lem302454 A P R n' _6689) (@lem302457 A P R n' _6689)). Qed.
Lemma lem302460 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : term1197 A n' f P R a.
Proof. exact (conj (@lem301871 A n x f a y P R n' h1 h2) (@lem302451 A n x f a y P R n' h1 h2)). Qed.
Lemma lem302462 {A : Type'} (_6689 : nat -> A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1195 A P R n' _6689.
Proof. exact (EQ_MP (@lem302458 A P R n' _6689) (@lem300843 A _6689 a y P R n' h1)). Qed.
Lemma lem302463 {A : Type'} (_6689 : nat -> A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1195 A P R n' _6689.
Proof. exact (@lem302462 A _6689 a y P R n' h1). Qed.
Lemma lem302464 {A : Type'} (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term316 A a y P R n') : term1198 A n' f P R a.
Proof. exact (@lem302463 A (term693 A f P R a) a y P R n' h1). Qed.
Lemma lem302467 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : False.
Proof. exact (@lem302464 A f a y P R n' h2 (@lem302460 A n x f a y P R n' h1 h2)). Qed.
Lemma lem302468 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : term1199.
Proof. exact (fun h0 : ~ False => @lem302467 A n x f a y P R n' h1 h2). Qed.
Lemma lem302470 (p : Prop) : (term1041 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem302471 : term1199 = False.
Proof. exact (@lem302470 False). Qed.
Lemma lem302472 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (n' : type977 A) (h1 : term683 A n x f) (h2 : term316 A a y P R n') : False.
Proof. exact (EQ_MP (@lem302471) (@lem302468 A n x f a y P R n' h1 h2)). Qed.
Lemma lem302473 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (y : type1596 A) (P : type1597 A) (R : type1594 A) (h1 : term683 A n x f) (h2 : term319 A a y P R) : False.
Proof. exact (ex_elim (@lem299798 A a y P R h2) (fun n' : type977 A => fun h0 : term318 A a y P R n' => @lem302472 A n x f a y P R n' h1 h0)). Qed.
Lemma lem302474 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (a : A) (P : type1597 A) (R : type1594 A) (h1 : term683 A n x f) (h2 : term321 A a P R) : False.
Proof. exact (ex_elim (@lem299797 A a P R h2) (fun y : type1596 A => fun h0 : term320 A a P R y => @lem302473 A n x f a y P R h1 h0)). Qed.
Lemma lem302475 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (R : type1594 A) (h1 : term683 A n x f) (h2 : term323 A P R) : False.
Proof. exact (ex_elim (@lem299796 A P R h2) (fun a : A => fun h0 : term322 A P R a => @lem302474 A n x f a P R h1 h0)). Qed.
Lemma lem302476 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (P : type1597 A) (h1 : term683 A n x f) (h2 : term325 A P) : False.
Proof. exact (ex_elim (@lem299795 A P h2) (fun R : type1594 A => fun h0 : term324 A P R => @lem302475 A n x f P R h1 h0)). Qed.
Lemma lem302477 {A : Type'} (n : type946 A) (x : type945 A) (f : type944 A) (h1 : term683 A n x f) (h2 : term10 A) : False.
Proof. exact (ex_elim (@lem299059 A h2) (fun P : type1597 A => fun h0 : term326 A P => @lem302476 A n x f P h1 h0)). Qed.
Lemma lem302478 {A : Type'} (n : type946 A) (x : type945 A) (h1 : term686 A n x) (h2 : term10 A) : False.
Proof. exact (ex_elim (@lem299793 A n x h1) (fun f : type944 A => fun h0 : term685 A n x f => @lem302477 A n x f h0 h2)). Qed.
Lemma lem302479 {A : Type'} (n : type946 A) (h1 : term688 A n) (h2 : term10 A) : False.
Proof. exact (ex_elim (@lem299792 A n h1) (fun x : type945 A => fun h0 : term687 A n x => @lem302478 A n x h0 h2)). Qed.
Lemma lem302480 {A : Type'} (h1 : term17 A) (h2 : term10 A) : False.
Proof. exact (ex_elim (@lem299791 A h1) (fun n : type946 A => fun h0 : term689 A n => @lem302479 A n h0 h2)). Qed.
Lemma lem302481 {A : Type'} (h1 : term10 A) : term15 A.
Proof. exact (fun h0 : term17 A => @lem302480 A h0 h1). Qed.
Lemma lem302482 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (@lem69 (term17 A)). Qed.
Lemma lem302483 {A : Type'} (h1 : term10 A) : term16 A.
Proof. exact (EQ_MP (@lem302482 A) (@lem302481 A h1)). Qed.
Lemma lem302484 {A : Type'} : term19 A.
Proof. exact (fun h0 : term10 A => @lem302483 A h0). Qed.
Lemma lem302485 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem298466 A) (@lem302484 A)). Qed.
Lemma lem302487 {A : Type'} : term11 A.
Proof. exact (@lem297940 A (@lem302485 A)). Qed.
Lemma lem302488 {A : Type'} (h1 : term10 A) : term15 A.
Proof. exact (@lem302487 A (@lem297924 A h1)). Qed.
Lemma lem302489 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem302488 A h1 (@lem297909 A)). Qed.
Lemma lem302490 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem302489 A h1) (fun h2 : False => @lem297924 A h1)). Qed.
Lemma lem302491 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem302490 A h1) (@lem297924 A h1)). Qed.
Lemma lem302492 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem302491 A h0). Qed.
Lemma lem302493 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem297923 A) (@lem302492 A)). Qed.
