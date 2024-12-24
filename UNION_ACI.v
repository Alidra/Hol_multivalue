Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_ACI_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3297132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3297133 {_86426 : Type'} (s : _86426 -> Prop) (t : _86426 -> Prop) : (s = t) = (term0 _86426 s t).
Proof. exact (@lem3297132 _86426 s t). Qed.
Lemma lem3297134 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : ((@UNION _86426 p q) = (@UNION _86426 q p)) = (term1 _86426 q p).
Proof. exact (@lem3297133 _86426 (@UNION _86426 p q) (@UNION _86426 q p)). Qed.
Lemma lem3297143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297144 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term2 _86426 q p) = (term3 _86426 q p).
Proof. exact (MK_COMB (@lem3297143) (@lem3297134 _86426 q p)). Qed.
Lemma lem3297150 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3297151 {_86426 : Type'} (s : _86426 -> Prop) (t : _86426 -> Prop) : (s = t) = (term0 _86426 s t).
Proof. exact (@lem3297150 _86426 s t). Qed.
Lemma lem3297152 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : ((term4 _86426 p q r) = (term5 _86426 p q r)) = (term6 _86426 p q r).
Proof. exact (@lem3297151 _86426 (term4 _86426 p q r) (term5 _86426 p q r)). Qed.
Lemma lem3297161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297162 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term7 _86426 p q r) = (term8 _86426 p q r).
Proof. exact (MK_COMB (@lem3297161) (@lem3297152 _86426 p q r)). Qed.
Lemma lem3297168 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3297169 {_86426 : Type'} (s : _86426 -> Prop) (t : _86426 -> Prop) : (s = t) = (term0 _86426 s t).
Proof. exact (@lem3297168 _86426 s t). Qed.
Lemma lem3297170 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : ((term5 _86426 p q r) = (term5 _86426 q p r)) = (term9 _86426 q p r).
Proof. exact (@lem3297169 _86426 (term5 _86426 p q r) (term5 _86426 q p r)). Qed.
Lemma lem3297179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297180 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term10 _86426 q p r) = (term11 _86426 q p r).
Proof. exact (MK_COMB (@lem3297179) (@lem3297170 _86426 q p r)). Qed.
Lemma lem3297186 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3297187 {_86426 : Type'} (s : _86426 -> Prop) (t : _86426 -> Prop) : (s = t) = (term0 _86426 s t).
Proof. exact (@lem3297186 _86426 s t). Qed.
Lemma lem3297188 {_86426 : Type'} (p : _86426 -> Prop) : ((@UNION _86426 p p) = p) = (term12 _86426 p).
Proof. exact (@lem3297187 _86426 (@UNION _86426 p p) p). Qed.
Lemma lem3297197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297198 {_86426 : Type'} (p : _86426 -> Prop) : (term13 _86426 p) = (term14 _86426 p).
Proof. exact (MK_COMB (@lem3297197) (@lem3297188 _86426 p)). Qed.
Lemma lem3297202 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3297203 {_86426 : Type'} (s : _86426 -> Prop) (t : _86426 -> Prop) : (s = t) = (term0 _86426 s t).
Proof. exact (@lem3297202 _86426 s t). Qed.
Lemma lem3297204 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term15 _86426 p q) = (@UNION _86426 p q)) = (term16 _86426 p q).
Proof. exact (@lem3297203 _86426 (term15 _86426 p q) (@UNION _86426 p q)). Qed.
Lemma lem3297213 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term17 _86426 p q) = (term18 _86426 p q).
Proof. exact (MK_COMB (@lem3297198 _86426 p) (@lem3297204 _86426 p q)). Qed.
Lemma lem3297216 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term19 _86426 r p q) = (term20 _86426 r p q).
Proof. exact (MK_COMB (@lem3297180 _86426 q p r) (@lem3297213 _86426 p q)). Qed.
Lemma lem3297219 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term21 _86426 r p q) = (term22 _86426 r p q).
Proof. exact (MK_COMB (@lem3297162 _86426 p q r) (@lem3297216 _86426 r p q)). Qed.
Lemma lem3297222 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term23 _86426 r p q) = (term24 _86426 r p q).
Proof. exact (MK_COMB (@lem3297144 _86426 q p) (@lem3297219 _86426 r p q)). Qed.
Lemma lem3297225 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term24 _86426 r p q) = (term23 _86426 r p q).
Proof. exact (SYM (@lem3297222 _86426 r p q)). Qed.
Lemma lem3297235 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297236 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297235 _86426 s x t). Qed.
Lemma lem3297237 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (q : _86426 -> Prop) : (term25 _86426 x p q) = (term26 _86426 p x q).
Proof. exact (@lem3297236 _86426 p x q). Qed.
Lemma lem3297241 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297242 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297241 _86426 P x). Qed.
Lemma lem3297243 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297242 _86426 p x). Qed.
Lemma lem3297244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297245 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297244) (@lem3297243 _86426 p x)). Qed.
Lemma lem3297247 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297248 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297247 _86426 P x). Qed.
Lemma lem3297249 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297248 _86426 q x). Qed.
Lemma lem3297250 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term26 _86426 p x q) = (term29 _86426 p q x).
Proof. exact (MK_COMB (@lem3297245 _86426 p x) (@lem3297249 _86426 q x)). Qed.
Lemma lem3297253 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term25 _86426 x p q) = (term29 _86426 p q x).
Proof. exact (TRANS (@lem3297237 _86426 p x q) (@lem3297250 _86426 p q x)). Qed.
Lemma lem3297254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297255 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term30 _86426 x p q) = (term31 _86426 p q x).
Proof. exact (MK_COMB (@lem3297254) (@lem3297253 _86426 p q x)). Qed.
Lemma lem3297257 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297258 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297257 _86426 s x t). Qed.
Lemma lem3297259 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (p : _86426 -> Prop) : (term25 _86426 x q p) = (term26 _86426 q x p).
Proof. exact (@lem3297258 _86426 q x p). Qed.
Lemma lem3297263 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297264 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297263 _86426 P x). Qed.
Lemma lem3297265 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297264 _86426 q x). Qed.
Lemma lem3297266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297267 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term27 _86426 x q) = (term28 _86426 q x).
Proof. exact (MK_COMB (@lem3297266) (@lem3297265 _86426 q x)). Qed.
Lemma lem3297269 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297270 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297269 _86426 P x). Qed.
Lemma lem3297271 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297270 _86426 p x). Qed.
Lemma lem3297272 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term26 _86426 q x p) = (term29 _86426 q p x).
Proof. exact (MK_COMB (@lem3297267 _86426 q x) (@lem3297271 _86426 p x)). Qed.
Lemma lem3297275 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term25 _86426 x q p) = (term29 _86426 q p x).
Proof. exact (TRANS (@lem3297259 _86426 q x p) (@lem3297272 _86426 q p x)). Qed.
Lemma lem3297276 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : ((term25 _86426 x p q) = (term25 _86426 x q p)) = ((term29 _86426 p q x) = (term29 _86426 q p x)).
Proof. exact (MK_COMB (@lem3297255 _86426 p q x) (@lem3297275 _86426 q p x)). Qed.
Lemma lem3297279 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term32 _86426 q p) = (term33 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3297276 _86426 q p x)). Qed.
Lemma lem3297280 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3297281 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term1 _86426 q p) = (term34 _86426 q p).
Proof. exact (MK_COMB (@lem3297280 _86426) (@lem3297279 _86426 q p)). Qed.
Lemma lem3297286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297287 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term3 _86426 q p) = (term35 _86426 q p).
Proof. exact (MK_COMB (@lem3297286) (@lem3297281 _86426 q p)). Qed.
Lemma lem3297297 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297298 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297297 _86426 s x t). Qed.
Lemma lem3297299 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) (r : _86426 -> Prop) : (term36 _86426 x p q r) = (term37 _86426 p q x r).
Proof. exact (@lem3297298 _86426 (@UNION _86426 p q) x r). Qed.
Lemma lem3297303 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297304 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297303 _86426 s x t). Qed.
Lemma lem3297305 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (q : _86426 -> Prop) : (term25 _86426 x p q) = (term26 _86426 p x q).
Proof. exact (@lem3297304 _86426 p x q). Qed.
Lemma lem3297309 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297310 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297309 _86426 P x). Qed.
Lemma lem3297311 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297310 _86426 p x). Qed.
Lemma lem3297312 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297313 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297312) (@lem3297311 _86426 p x)). Qed.
Lemma lem3297315 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297316 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297315 _86426 P x). Qed.
Lemma lem3297317 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297316 _86426 q x). Qed.
Lemma lem3297318 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term26 _86426 p x q) = (term29 _86426 p q x).
Proof. exact (MK_COMB (@lem3297313 _86426 p x) (@lem3297317 _86426 q x)). Qed.
Lemma lem3297321 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term25 _86426 x p q) = (term29 _86426 p q x).
Proof. exact (TRANS (@lem3297305 _86426 p x q) (@lem3297318 _86426 p q x)). Qed.
Lemma lem3297322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297323 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term38 _86426 x p q) = (term39 _86426 p q x).
Proof. exact (MK_COMB (@lem3297322) (@lem3297321 _86426 p q x)). Qed.
Lemma lem3297325 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297326 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297325 _86426 P x). Qed.
Lemma lem3297327 {_86426 : Type'} (r : _86426 -> Prop) (x : _86426) : (@IN _86426 x r) = (r x).
Proof. exact (@lem3297326 _86426 r x). Qed.
Lemma lem3297328 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term37 _86426 p q x r) = (term40 _86426 p q r x).
Proof. exact (MK_COMB (@lem3297323 _86426 p q x) (@lem3297327 _86426 r x)). Qed.
Lemma lem3297331 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term36 _86426 x p q r) = (term40 _86426 p q r x).
Proof. exact (TRANS (@lem3297299 _86426 p q x r) (@lem3297328 _86426 p q r x)). Qed.
Lemma lem3297332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297333 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term41 _86426 x p q r) = (term42 _86426 p q r x).
Proof. exact (MK_COMB (@lem3297332) (@lem3297331 _86426 p q r x)). Qed.
Lemma lem3297335 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297336 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297335 _86426 s x t). Qed.
Lemma lem3297337 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term43 _86426 x p q r) = (term44 _86426 p x q r).
Proof. exact (@lem3297336 _86426 p x (@UNION _86426 q r)). Qed.
Lemma lem3297341 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297342 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297341 _86426 P x). Qed.
Lemma lem3297343 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297342 _86426 p x). Qed.
Lemma lem3297344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297345 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297344) (@lem3297343 _86426 p x)). Qed.
Lemma lem3297347 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297348 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297347 _86426 s x t). Qed.
Lemma lem3297349 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (r : _86426 -> Prop) : (term25 _86426 x q r) = (term26 _86426 q x r).
Proof. exact (@lem3297348 _86426 q x r). Qed.
Lemma lem3297353 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297354 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297353 _86426 P x). Qed.
Lemma lem3297355 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297354 _86426 q x). Qed.
Lemma lem3297356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297357 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term27 _86426 x q) = (term28 _86426 q x).
Proof. exact (MK_COMB (@lem3297356) (@lem3297355 _86426 q x)). Qed.
Lemma lem3297359 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297360 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297359 _86426 P x). Qed.
Lemma lem3297361 {_86426 : Type'} (r : _86426 -> Prop) (x : _86426) : (@IN _86426 x r) = (r x).
Proof. exact (@lem3297360 _86426 r x). Qed.
Lemma lem3297362 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term26 _86426 q x r) = (term29 _86426 q r x).
Proof. exact (MK_COMB (@lem3297357 _86426 q x) (@lem3297361 _86426 r x)). Qed.
Lemma lem3297365 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term25 _86426 x q r) = (term29 _86426 q r x).
Proof. exact (TRANS (@lem3297349 _86426 q x r) (@lem3297362 _86426 q r x)). Qed.
Lemma lem3297366 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term44 _86426 p x q r) = (term45 _86426 p q r x).
Proof. exact (MK_COMB (@lem3297345 _86426 p x) (@lem3297365 _86426 q r x)). Qed.
Lemma lem3297369 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term43 _86426 x p q r) = (term45 _86426 p q r x).
Proof. exact (TRANS (@lem3297337 _86426 p x q r) (@lem3297366 _86426 p q r x)). Qed.
Lemma lem3297370 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : ((term36 _86426 x p q r) = (term43 _86426 x p q r)) = ((term40 _86426 p q r x) = (term45 _86426 p q r x)).
Proof. exact (MK_COMB (@lem3297333 _86426 p q r x) (@lem3297369 _86426 p q r x)). Qed.
Lemma lem3297373 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term46 _86426 p q r) = (term47 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3297370 _86426 p q r x)). Qed.
Lemma lem3297374 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3297375 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term6 _86426 p q r) = (term48 _86426 p q r).
Proof. exact (MK_COMB (@lem3297374 _86426) (@lem3297373 _86426 p q r)). Qed.
Lemma lem3297380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297381 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term8 _86426 p q r) = (term49 _86426 p q r).
Proof. exact (MK_COMB (@lem3297380) (@lem3297375 _86426 p q r)). Qed.
Lemma lem3297391 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297392 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297391 _86426 s x t). Qed.
Lemma lem3297393 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term43 _86426 x p q r) = (term44 _86426 p x q r).
Proof. exact (@lem3297392 _86426 p x (@UNION _86426 q r)). Qed.
Lemma lem3297397 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297398 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297397 _86426 P x). Qed.
Lemma lem3297399 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297398 _86426 p x). Qed.
Lemma lem3297400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297401 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297400) (@lem3297399 _86426 p x)). Qed.
Lemma lem3297403 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297404 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297403 _86426 s x t). Qed.
Lemma lem3297405 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (r : _86426 -> Prop) : (term25 _86426 x q r) = (term26 _86426 q x r).
Proof. exact (@lem3297404 _86426 q x r). Qed.
Lemma lem3297409 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297410 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297409 _86426 P x). Qed.
Lemma lem3297411 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297410 _86426 q x). Qed.
Lemma lem3297412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297413 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term27 _86426 x q) = (term28 _86426 q x).
Proof. exact (MK_COMB (@lem3297412) (@lem3297411 _86426 q x)). Qed.
Lemma lem3297415 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297416 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297415 _86426 P x). Qed.
Lemma lem3297417 {_86426 : Type'} (r : _86426 -> Prop) (x : _86426) : (@IN _86426 x r) = (r x).
Proof. exact (@lem3297416 _86426 r x). Qed.
Lemma lem3297418 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term26 _86426 q x r) = (term29 _86426 q r x).
Proof. exact (MK_COMB (@lem3297413 _86426 q x) (@lem3297417 _86426 r x)). Qed.
Lemma lem3297421 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term25 _86426 x q r) = (term29 _86426 q r x).
Proof. exact (TRANS (@lem3297405 _86426 q x r) (@lem3297418 _86426 q r x)). Qed.
Lemma lem3297422 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term44 _86426 p x q r) = (term45 _86426 p q r x).
Proof. exact (MK_COMB (@lem3297401 _86426 p x) (@lem3297421 _86426 q r x)). Qed.
Lemma lem3297425 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term43 _86426 x p q r) = (term45 _86426 p q r x).
Proof. exact (TRANS (@lem3297393 _86426 p x q r) (@lem3297422 _86426 p q r x)). Qed.
Lemma lem3297426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297427 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term50 _86426 x p q r) = (term51 _86426 p q r x).
Proof. exact (MK_COMB (@lem3297426) (@lem3297425 _86426 p q r x)). Qed.
Lemma lem3297429 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297430 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297429 _86426 s x t). Qed.
Lemma lem3297431 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term43 _86426 x q p r) = (term44 _86426 q x p r).
Proof. exact (@lem3297430 _86426 q x (@UNION _86426 p r)). Qed.
Lemma lem3297435 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297436 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297435 _86426 P x). Qed.
Lemma lem3297437 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297436 _86426 q x). Qed.
Lemma lem3297438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297439 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term27 _86426 x q) = (term28 _86426 q x).
Proof. exact (MK_COMB (@lem3297438) (@lem3297437 _86426 q x)). Qed.
Lemma lem3297441 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297442 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297441 _86426 s x t). Qed.
Lemma lem3297443 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (r : _86426 -> Prop) : (term25 _86426 x p r) = (term26 _86426 p x r).
Proof. exact (@lem3297442 _86426 p x r). Qed.
Lemma lem3297447 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297448 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297447 _86426 P x). Qed.
Lemma lem3297449 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297448 _86426 p x). Qed.
Lemma lem3297450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297451 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297450) (@lem3297449 _86426 p x)). Qed.
Lemma lem3297453 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297454 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297453 _86426 P x). Qed.
Lemma lem3297455 {_86426 : Type'} (r : _86426 -> Prop) (x : _86426) : (@IN _86426 x r) = (r x).
Proof. exact (@lem3297454 _86426 r x). Qed.
Lemma lem3297456 {_86426 : Type'} (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term26 _86426 p x r) = (term29 _86426 p r x).
Proof. exact (MK_COMB (@lem3297451 _86426 p x) (@lem3297455 _86426 r x)). Qed.
Lemma lem3297459 {_86426 : Type'} (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term25 _86426 x p r) = (term29 _86426 p r x).
Proof. exact (TRANS (@lem3297443 _86426 p x r) (@lem3297456 _86426 p r x)). Qed.
Lemma lem3297460 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term44 _86426 q x p r) = (term45 _86426 q p r x).
Proof. exact (MK_COMB (@lem3297439 _86426 q x) (@lem3297459 _86426 p r x)). Qed.
Lemma lem3297463 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term43 _86426 x q p r) = (term45 _86426 q p r x).
Proof. exact (TRANS (@lem3297431 _86426 q x p r) (@lem3297460 _86426 q p r x)). Qed.
Lemma lem3297464 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : ((term43 _86426 x p q r) = (term43 _86426 x q p r)) = ((term45 _86426 p q r x) = (term45 _86426 q p r x)).
Proof. exact (MK_COMB (@lem3297427 _86426 p q r x) (@lem3297463 _86426 q p r x)). Qed.
Lemma lem3297467 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term52 _86426 q p r) = (term53 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3297464 _86426 q p r x)). Qed.
Lemma lem3297468 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3297469 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term9 _86426 q p r) = (term54 _86426 q p r).
Proof. exact (MK_COMB (@lem3297468 _86426) (@lem3297467 _86426 q p r)). Qed.
Lemma lem3297474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297475 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term11 _86426 q p r) = (term55 _86426 q p r).
Proof. exact (MK_COMB (@lem3297474) (@lem3297469 _86426 q p r)). Qed.
Lemma lem3297485 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297486 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297485 _86426 s x t). Qed.
Lemma lem3297487 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) : (term56 _86426 x p) = (term57 _86426 x p).
Proof. exact (@lem3297486 _86426 p x p). Qed.
Lemma lem3297489 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem3297490 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) : (term57 _86426 x p) = (@IN _86426 x p).
Proof. exact (@lem3297489 (@IN _86426 x p)). Qed.
Lemma lem3297492 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297493 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297492 _86426 P x). Qed.
Lemma lem3297494 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297493 _86426 p x). Qed.
Lemma lem3297495 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term57 _86426 x p) = (p x).
Proof. exact (TRANS (@lem3297490 _86426 x p) (@lem3297494 _86426 p x)). Qed.
Lemma lem3297496 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term56 _86426 x p) = (p x).
Proof. exact (TRANS (@lem3297487 _86426 x p) (@lem3297495 _86426 p x)). Qed.
Lemma lem3297497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297498 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term58 _86426 x p) = (term59 _86426 p x).
Proof. exact (MK_COMB (@lem3297497) (@lem3297496 _86426 p x)). Qed.
Lemma lem3297500 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297501 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297500 _86426 P x). Qed.
Lemma lem3297502 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297501 _86426 p x). Qed.
Lemma lem3297503 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : ((term56 _86426 x p) = (@IN _86426 x p)) = ((p x) = (p x)).
Proof. exact (MK_COMB (@lem3297498 _86426 p x) (@lem3297502 _86426 p x)). Qed.
Lemma lem3297505 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3297506 (x : Prop) : (x = x) = True.
Proof. exact (@lem3297505 Prop x). Qed.
Lemma lem3297507 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : ((p x) = (p x)) = True.
Proof. exact (@lem3297506 (p x)). Qed.
Lemma lem3297508 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) : ((term56 _86426 x p) = (@IN _86426 x p)) = True.
Proof. exact (TRANS (@lem3297503 _86426 p x) (@lem3297507 _86426 p x)). Qed.
Lemma lem3297509 {_86426 : Type'} (p : _86426 -> Prop) : (term60 _86426 p) = (term61 _86426).
Proof. exact (fun_ext (fun x : _86426 => @lem3297508 _86426 x p)). Qed.
Lemma lem3297510 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3297511 {_86426 : Type'} (p : _86426 -> Prop) : (term12 _86426 p) = (term62 _86426).
Proof. exact (MK_COMB (@lem3297510 _86426) (@lem3297509 _86426 p)). Qed.
Lemma lem3297513 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3297514 {_86426 : Type'} (t : Prop) : (term63 _86426 t) = t.
Proof. exact (@lem3297513 _86426 t). Qed.
Lemma lem3297515 {_86426 : Type'} : (term62 _86426) = True.
Proof. exact (@lem3297514 _86426 True). Qed.
Lemma lem3297516 {_86426 : Type'} (p : _86426 -> Prop) : (term12 _86426 p) = True.
Proof. exact (TRANS (@lem3297511 _86426 p) (@lem3297515 _86426)). Qed.
Lemma lem3297517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297518 {_86426 : Type'} (p : _86426 -> Prop) : (term14 _86426 p) = (and True).
Proof. exact (MK_COMB (@lem3297517) (@lem3297516 _86426 p)). Qed.
Lemma lem3297526 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297527 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297526 _86426 s x t). Qed.
Lemma lem3297528 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term64 _86426 x p q) = (term65 _86426 x p q).
Proof. exact (@lem3297527 _86426 p x (@UNION _86426 p q)). Qed.
Lemma lem3297532 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297533 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297532 _86426 P x). Qed.
Lemma lem3297534 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297533 _86426 p x). Qed.
Lemma lem3297535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297536 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297535) (@lem3297534 _86426 p x)). Qed.
Lemma lem3297538 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297539 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297538 _86426 s x t). Qed.
Lemma lem3297540 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (q : _86426 -> Prop) : (term25 _86426 x p q) = (term26 _86426 p x q).
Proof. exact (@lem3297539 _86426 p x q). Qed.
Lemma lem3297544 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297545 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297544 _86426 P x). Qed.
Lemma lem3297546 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297545 _86426 p x). Qed.
Lemma lem3297547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297548 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297547) (@lem3297546 _86426 p x)). Qed.
Lemma lem3297550 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297551 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297550 _86426 P x). Qed.
Lemma lem3297552 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297551 _86426 q x). Qed.
Lemma lem3297553 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term26 _86426 p x q) = (term29 _86426 p q x).
Proof. exact (MK_COMB (@lem3297548 _86426 p x) (@lem3297552 _86426 q x)). Qed.
Lemma lem3297556 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term25 _86426 x p q) = (term29 _86426 p q x).
Proof. exact (TRANS (@lem3297540 _86426 p x q) (@lem3297553 _86426 p q x)). Qed.
Lemma lem3297557 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term65 _86426 x p q) = (term66 _86426 p q x).
Proof. exact (MK_COMB (@lem3297536 _86426 p x) (@lem3297556 _86426 p q x)). Qed.
Lemma lem3297560 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term64 _86426 x p q) = (term66 _86426 p q x).
Proof. exact (TRANS (@lem3297528 _86426 x p q) (@lem3297557 _86426 p q x)). Qed.
Lemma lem3297561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297562 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term67 _86426 x p q) = (term68 _86426 p q x).
Proof. exact (MK_COMB (@lem3297561) (@lem3297560 _86426 p q x)). Qed.
Lemma lem3297564 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3297565 {_86426 : Type'} (s : _86426 -> Prop) (x : _86426) (t : _86426 -> Prop) : (term25 _86426 x s t) = (term26 _86426 s x t).
Proof. exact (@lem3297564 _86426 s x t). Qed.
Lemma lem3297566 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (q : _86426 -> Prop) : (term25 _86426 x p q) = (term26 _86426 p x q).
Proof. exact (@lem3297565 _86426 p x q). Qed.
Lemma lem3297570 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297571 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297570 _86426 P x). Qed.
Lemma lem3297572 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (@IN _86426 x p) = (p x).
Proof. exact (@lem3297571 _86426 p x). Qed.
Lemma lem3297573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3297574 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term27 _86426 x p) = (term28 _86426 p x).
Proof. exact (MK_COMB (@lem3297573) (@lem3297572 _86426 p x)). Qed.
Lemma lem3297576 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3297577 {_86426 : Type'} (P : _86426 -> Prop) (x : _86426) : (@IN _86426 x P) = (P x).
Proof. exact (@lem3297576 _86426 P x). Qed.
Lemma lem3297578 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (@IN _86426 x q) = (q x).
Proof. exact (@lem3297577 _86426 q x). Qed.
Lemma lem3297579 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term26 _86426 p x q) = (term29 _86426 p q x).
Proof. exact (MK_COMB (@lem3297574 _86426 p x) (@lem3297578 _86426 q x)). Qed.
Lemma lem3297582 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term25 _86426 x p q) = (term29 _86426 p q x).
Proof. exact (TRANS (@lem3297566 _86426 p x q) (@lem3297579 _86426 p q x)). Qed.
Lemma lem3297583 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : ((term64 _86426 x p q) = (term25 _86426 x p q)) = ((term66 _86426 p q x) = (term29 _86426 p q x)).
Proof. exact (MK_COMB (@lem3297562 _86426 p q x) (@lem3297582 _86426 p q x)). Qed.
Lemma lem3297586 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term69 _86426 p q) = (term70 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3297583 _86426 p q x)). Qed.
Lemma lem3297587 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3297588 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term16 _86426 p q) = (term71 _86426 p q).
Proof. exact (MK_COMB (@lem3297587 _86426) (@lem3297586 _86426 p q)). Qed.
Lemma lem3297593 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term18 _86426 p q) = (term72 _86426 p q).
Proof. exact (MK_COMB (@lem3297518 _86426 p) (@lem3297588 _86426 p q)). Qed.
Lemma lem3297595 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3297596 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term72 _86426 p q) = (term71 _86426 p q).
Proof. exact (@lem3297595 (term71 _86426 p q)). Qed.
Lemma lem3297609 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term18 _86426 p q) = (term71 _86426 p q).
Proof. exact (TRANS (@lem3297593 _86426 p q) (@lem3297596 _86426 p q)). Qed.
Lemma lem3297610 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term20 _86426 r p q) = (term73 _86426 r p q).
Proof. exact (MK_COMB (@lem3297475 _86426 q p r) (@lem3297609 _86426 p q)). Qed.
Lemma lem3297613 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term22 _86426 r p q) = (term74 _86426 r p q).
Proof. exact (MK_COMB (@lem3297381 _86426 p q r) (@lem3297610 _86426 r p q)). Qed.
Lemma lem3297616 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term24 _86426 r p q) = (term75 _86426 r p q).
Proof. exact (MK_COMB (@lem3297287 _86426 q p) (@lem3297613 _86426 r p q)). Qed.
Lemma lem3297619 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term75 _86426 r p q) = (term24 _86426 r p q).
Proof. exact (SYM (@lem3297616 _86426 r p q)). Qed.
Lemma lem3297621 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3297622 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term75 _86426 r p q) = (term77 _86426 r p q).
Proof. exact (@lem3297621 (term75 _86426 r p q)). Qed.
Lemma lem3297623 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term77 _86426 r p q) = (term75 _86426 r p q).
Proof. exact (SYM (@lem3297622 _86426 r p q)). Qed.
Lemma lem3297624 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term78 _86426 r p q) : term78 _86426 r p q.
Proof. exact (h1). Qed.
Lemma lem3297627 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term77 _86426 r p q) : term77 _86426 r p q.
Proof. exact (h1). Qed.
Lemma lem3297628 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term79 _86426 r p q.
Proof. exact (fun h0 : term77 _86426 r p q => @lem3297627 _86426 r p q h0). Qed.
Lemma lem3297629 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term79 _86426 r p q) : term79 _86426 r p q.
Proof. exact (h1). Qed.
Lemma lem3297630 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term77 _86426 r p q) : term77 _86426 r p q.
Proof. exact (h1). Qed.
Lemma lem3297631 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term77 _86426 r p q) (h2 : term79 _86426 r p q) : term77 _86426 r p q.
Proof. exact (@lem3297629 _86426 r p q h2 (@lem3297630 _86426 r p q h1)). Qed.
Lemma lem3297632 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term77 _86426 r p q) : term80 _86426 r p q.
Proof. exact (fun h0 : term79 _86426 r p q => @lem3297631 _86426 r p q h1 h0). Qed.
Lemma lem3297633 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term79 _86426 r p q) : term79 _86426 r p q.
Proof. exact (h1). Qed.
Lemma lem3297634 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term77 _86426 r p q) (h2 : term79 _86426 r p q) : term77 _86426 r p q.
Proof. exact (@lem3297632 _86426 r p q h1 (@lem3297633 _86426 r p q h2)). Qed.
Lemma lem3297635 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term79 _86426 r p q) : term79 _86426 r p q.
Proof. exact (fun h0 : term77 _86426 r p q => @lem3297634 _86426 r p q h0 h1). Qed.
Lemma lem3297636 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term81 _86426 r p q.
Proof. exact (fun h0 : term79 _86426 r p q => @lem3297635 _86426 r p q h0). Qed.
Lemma lem3297639 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term79 _86426 r p q.
Proof. exact (@lem3297636 _86426 r p q (@lem3297628 _86426 r p q)). Qed.
Lemma lem3297640 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term79 _86426 r p q.
Proof. exact (@lem3297639 _86426 r p q). Qed.
Lemma lem3297654 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3297655 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term77 _86426 r p q) = (term82 _86426 r p q).
Proof. exact (@lem3297654 (term78 _86426 r p q)). Qed.
Lemma lem3297657 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3297658 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term82 _86426 r p q) = (term75 _86426 r p q).
Proof. exact (@lem3297657 (term75 _86426 r p q)). Qed.
Lemma lem3297661 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term77 _86426 r p q) = (term75 _86426 r p q).
Proof. exact (TRANS (@lem3297655 _86426 r p q) (@lem3297658 _86426 r p q)). Qed.
Lemma lem3297708 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term84 _86426 p q) = (term85 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297661 _86426 r p q)). Qed.
Lemma lem3297709 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297710 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term86 _86426 p q) = (term87 _86426 p q).
Proof. exact (MK_COMB (@lem3297709 _86426) (@lem3297708 _86426 p q)). Qed.
Lemma lem3297712 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3297713 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3297712 (_86426 -> Prop) P Q). Qed.
Lemma lem3297714 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term92 _86426 p q) = (term93 _86426 p q).
Proof. exact (@lem3297713 _86426 (term94 _86426 q p) (term95 _86426 p q)). Qed.
Lemma lem3297715 {_86426 : Type'} (r : _86426 -> Prop) (q : _86426 -> Prop) (p : _86426 -> Prop) : (term96 _86426 q p r) = (term34 _86426 q p).
Proof. exact (eq_refl (term96 _86426 q p r)). Qed.
Lemma lem3297716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297717 {_86426 : Type'} (r : _86426 -> Prop) (q : _86426 -> Prop) (p : _86426 -> Prop) : (term97 _86426 q p r) = (term35 _86426 q p).
Proof. exact (MK_COMB (@lem3297716) (@lem3297715 _86426 r q p)). Qed.
Lemma lem3297718 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term98 _86426 p q r) = (term74 _86426 r p q).
Proof. exact (eq_refl (term98 _86426 p q r)). Qed.
Lemma lem3297719 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term99 _86426 p q r) = (term75 _86426 r p q).
Proof. exact (MK_COMB (@lem3297717 _86426 r q p) (@lem3297718 _86426 r p q)). Qed.
Lemma lem3297720 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term100 _86426 p q) = (term85 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297719 _86426 r p q)). Qed.
Lemma lem3297721 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297722 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term92 _86426 p q) = (term87 _86426 p q).
Proof. exact (MK_COMB (@lem3297721 _86426) (@lem3297720 _86426 p q)). Qed.
Lemma lem3297723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297724 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term101 _86426 p q) = (term102 _86426 p q).
Proof. exact (MK_COMB (@lem3297723) (@lem3297722 _86426 p q)). Qed.
Lemma lem3297725 {_86426 : Type'} (r : _86426 -> Prop) (q : _86426 -> Prop) (p : _86426 -> Prop) : (term96 _86426 q p r) = (term34 _86426 q p).
Proof. exact (eq_refl (term96 _86426 q p r)). Qed.
Lemma lem3297726 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term103 _86426 q p) = (term94 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297725 _86426 r q p)). Qed.
Lemma lem3297727 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297728 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term104 _86426 q p) = (term105 _86426 q p).
Proof. exact (MK_COMB (@lem3297727 _86426) (@lem3297726 _86426 q p)). Qed.
Lemma lem3297729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297730 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term106 _86426 q p) = (term107 _86426 q p).
Proof. exact (MK_COMB (@lem3297729) (@lem3297728 _86426 q p)). Qed.
Lemma lem3297731 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term98 _86426 p q r) = (term74 _86426 r p q).
Proof. exact (eq_refl (term98 _86426 p q r)). Qed.
Lemma lem3297732 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term108 _86426 p q) = (term95 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297731 _86426 r p q)). Qed.
Lemma lem3297733 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297734 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term109 _86426 p q) = (term110 _86426 p q).
Proof. exact (MK_COMB (@lem3297733 _86426) (@lem3297732 _86426 p q)). Qed.
Lemma lem3297735 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term93 _86426 p q) = (term111 _86426 p q).
Proof. exact (MK_COMB (@lem3297730 _86426 q p) (@lem3297734 _86426 p q)). Qed.
Lemma lem3297736 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term92 _86426 p q) = (term93 _86426 p q)) = ((term87 _86426 p q) = (term111 _86426 p q)).
Proof. exact (MK_COMB (@lem3297724 _86426 p q) (@lem3297735 _86426 p q)). Qed.
Lemma lem3297737 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term87 _86426 p q) = (term111 _86426 p q).
Proof. exact (EQ_MP (@lem3297736 _86426 p q) (@lem3297714 _86426 p q)). Qed.
Lemma lem3297741 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem3297742 {_86426 : Type'} (t : Prop) : (term112 _86426 t) = t.
Proof. exact (@lem3297741 (_86426 -> Prop) t). Qed.
Lemma lem3297743 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term105 _86426 q p) = (term34 _86426 q p).
Proof. exact (@lem3297742 _86426 (term34 _86426 q p)). Qed.
Lemma lem3297752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297753 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term107 _86426 q p) = (term35 _86426 q p).
Proof. exact (MK_COMB (@lem3297752) (@lem3297743 _86426 q p)). Qed.
Lemma lem3297755 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3297756 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3297755 (_86426 -> Prop) P Q). Qed.
Lemma lem3297757 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term113 _86426 p q) = (term114 _86426 p q).
Proof. exact (@lem3297756 _86426 (term115 _86426 p q) (term116 _86426 p q)). Qed.
Lemma lem3297758 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term117 _86426 p q r) = (term48 _86426 p q r).
Proof. exact (eq_refl (term117 _86426 p q r)). Qed.
Lemma lem3297759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297760 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term118 _86426 p q r) = (term49 _86426 p q r).
Proof. exact (MK_COMB (@lem3297759) (@lem3297758 _86426 p q r)). Qed.
Lemma lem3297761 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term119 _86426 p q r) = (term73 _86426 r p q).
Proof. exact (eq_refl (term119 _86426 p q r)). Qed.
Lemma lem3297762 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term120 _86426 p q r) = (term74 _86426 r p q).
Proof. exact (MK_COMB (@lem3297760 _86426 p q r) (@lem3297761 _86426 r p q)). Qed.
Lemma lem3297763 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term121 _86426 p q) = (term95 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297762 _86426 r p q)). Qed.
Lemma lem3297764 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297765 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term113 _86426 p q) = (term110 _86426 p q).
Proof. exact (MK_COMB (@lem3297764 _86426) (@lem3297763 _86426 p q)). Qed.
Lemma lem3297766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297767 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term122 _86426 p q) = (term123 _86426 p q).
Proof. exact (MK_COMB (@lem3297766) (@lem3297765 _86426 p q)). Qed.
Lemma lem3297768 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term117 _86426 p q r) = (term48 _86426 p q r).
Proof. exact (eq_refl (term117 _86426 p q r)). Qed.
Lemma lem3297769 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term124 _86426 p q) = (term115 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297768 _86426 p q r)). Qed.
Lemma lem3297770 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297771 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term125 _86426 p q) = (term126 _86426 p q).
Proof. exact (MK_COMB (@lem3297770 _86426) (@lem3297769 _86426 p q)). Qed.
Lemma lem3297772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297773 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term127 _86426 p q) = (term128 _86426 p q).
Proof. exact (MK_COMB (@lem3297772) (@lem3297771 _86426 p q)). Qed.
Lemma lem3297774 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term119 _86426 p q r) = (term73 _86426 r p q).
Proof. exact (eq_refl (term119 _86426 p q r)). Qed.
Lemma lem3297775 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term129 _86426 p q) = (term116 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297774 _86426 r p q)). Qed.
Lemma lem3297776 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297777 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term130 _86426 p q) = (term131 _86426 p q).
Proof. exact (MK_COMB (@lem3297776 _86426) (@lem3297775 _86426 p q)). Qed.
Lemma lem3297778 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term114 _86426 p q) = (term132 _86426 p q).
Proof. exact (MK_COMB (@lem3297773 _86426 p q) (@lem3297777 _86426 p q)). Qed.
Lemma lem3297779 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term113 _86426 p q) = (term114 _86426 p q)) = ((term110 _86426 p q) = (term132 _86426 p q)).
Proof. exact (MK_COMB (@lem3297767 _86426 p q) (@lem3297778 _86426 p q)). Qed.
Lemma lem3297780 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term110 _86426 p q) = (term132 _86426 p q).
Proof. exact (EQ_MP (@lem3297779 _86426 p q) (@lem3297757 _86426 p q)). Qed.
Lemma lem3297800 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3297801 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3297800 (_86426 -> Prop) P Q). Qed.
Lemma lem3297802 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term133 _86426 p q) = (term134 _86426 p q).
Proof. exact (@lem3297801 _86426 (term135 _86426 q p) (term136 _86426 p q)). Qed.
Lemma lem3297803 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term137 _86426 q p r) = (term54 _86426 q p r).
Proof. exact (eq_refl (term137 _86426 q p r)). Qed.
Lemma lem3297804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297805 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term138 _86426 q p r) = (term55 _86426 q p r).
Proof. exact (MK_COMB (@lem3297804) (@lem3297803 _86426 q p r)). Qed.
Lemma lem3297806 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term139 _86426 p q r) = (term71 _86426 p q).
Proof. exact (eq_refl (term139 _86426 p q r)). Qed.
Lemma lem3297807 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term140 _86426 p q r) = (term73 _86426 r p q).
Proof. exact (MK_COMB (@lem3297805 _86426 q p r) (@lem3297806 _86426 r p q)). Qed.
Lemma lem3297808 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term141 _86426 p q) = (term116 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297807 _86426 r p q)). Qed.
Lemma lem3297809 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297810 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term133 _86426 p q) = (term131 _86426 p q).
Proof. exact (MK_COMB (@lem3297809 _86426) (@lem3297808 _86426 p q)). Qed.
Lemma lem3297811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297812 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term142 _86426 p q) = (term143 _86426 p q).
Proof. exact (MK_COMB (@lem3297811) (@lem3297810 _86426 p q)). Qed.
Lemma lem3297813 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term137 _86426 q p r) = (term54 _86426 q p r).
Proof. exact (eq_refl (term137 _86426 q p r)). Qed.
Lemma lem3297814 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term144 _86426 q p) = (term135 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297813 _86426 q p r)). Qed.
Lemma lem3297815 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297816 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term145 _86426 q p) = (term146 _86426 q p).
Proof. exact (MK_COMB (@lem3297815 _86426) (@lem3297814 _86426 q p)). Qed.
Lemma lem3297817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297818 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term147 _86426 q p) = (term148 _86426 q p).
Proof. exact (MK_COMB (@lem3297817) (@lem3297816 _86426 q p)). Qed.
Lemma lem3297819 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term139 _86426 p q r) = (term71 _86426 p q).
Proof. exact (eq_refl (term139 _86426 p q r)). Qed.
Lemma lem3297820 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term149 _86426 p q) = (term136 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3297819 _86426 r p q)). Qed.
Lemma lem3297821 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297822 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term150 _86426 p q) = (term151 _86426 p q).
Proof. exact (MK_COMB (@lem3297821 _86426) (@lem3297820 _86426 p q)). Qed.
Lemma lem3297823 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term134 _86426 p q) = (term152 _86426 p q).
Proof. exact (MK_COMB (@lem3297818 _86426 q p) (@lem3297822 _86426 p q)). Qed.
Lemma lem3297824 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term133 _86426 p q) = (term134 _86426 p q)) = ((term131 _86426 p q) = (term152 _86426 p q)).
Proof. exact (MK_COMB (@lem3297812 _86426 p q) (@lem3297823 _86426 p q)). Qed.
Lemma lem3297825 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term131 _86426 p q) = (term152 _86426 p q).
Proof. exact (EQ_MP (@lem3297824 _86426 p q) (@lem3297802 _86426 p q)). Qed.
Lemma lem3297845 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem3297846 {_86426 : Type'} (t : Prop) : (term112 _86426 t) = t.
Proof. exact (@lem3297845 (_86426 -> Prop) t). Qed.
Lemma lem3297847 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term151 _86426 p q) = (term71 _86426 p q).
Proof. exact (@lem3297846 _86426 (term71 _86426 p q)). Qed.
Lemma lem3297858 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term148 _86426 q p) = (term148 _86426 q p).
Proof. exact (eq_refl (term148 _86426 q p)). Qed.
Lemma lem3297859 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term152 _86426 p q) = (term153 _86426 p q).
Proof. exact (MK_COMB (@lem3297858 _86426 q p) (@lem3297847 _86426 p q)). Qed.
Lemma lem3297862 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term131 _86426 p q) = (term153 _86426 p q).
Proof. exact (TRANS (@lem3297825 _86426 p q) (@lem3297859 _86426 p q)). Qed.
Lemma lem3297863 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term128 _86426 p q) = (term128 _86426 p q).
Proof. exact (eq_refl (term128 _86426 p q)). Qed.
Lemma lem3297864 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term132 _86426 p q) = (term154 _86426 p q).
Proof. exact (MK_COMB (@lem3297863 _86426 p q) (@lem3297862 _86426 p q)). Qed.
Lemma lem3297867 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term110 _86426 p q) = (term154 _86426 p q).
Proof. exact (TRANS (@lem3297780 _86426 p q) (@lem3297864 _86426 p q)). Qed.
Lemma lem3297868 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term111 _86426 p q) = (term155 _86426 p q).
Proof. exact (MK_COMB (@lem3297753 _86426 q p) (@lem3297867 _86426 p q)). Qed.
Lemma lem3297871 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term87 _86426 p q) = (term155 _86426 p q).
Proof. exact (TRANS (@lem3297737 _86426 p q) (@lem3297868 _86426 p q)). Qed.
Lemma lem3297872 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term86 _86426 p q) = (term155 _86426 p q).
Proof. exact (TRANS (@lem3297710 _86426 p q) (@lem3297871 _86426 p q)). Qed.
Lemma lem3297873 {_86426 : Type'} (q : _86426 -> Prop) : (term156 _86426 q) = (term157 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297872 _86426 p q)). Qed.
Lemma lem3297874 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297875 {_86426 : Type'} (q : _86426 -> Prop) : (term158 _86426 q) = (term159 _86426 q).
Proof. exact (MK_COMB (@lem3297874 _86426) (@lem3297873 _86426 q)). Qed.
Lemma lem3297877 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3297878 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3297877 (_86426 -> Prop) P Q). Qed.
Lemma lem3297879 {_86426 : Type'} (q : _86426 -> Prop) : (term160 _86426 q) = (term161 _86426 q).
Proof. exact (@lem3297878 _86426 (term162 _86426 q) (term163 _86426 q)). Qed.
Lemma lem3297880 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term164 _86426 q p) = (term34 _86426 q p).
Proof. exact (eq_refl (term164 _86426 q p)). Qed.
Lemma lem3297881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297882 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term165 _86426 q p) = (term35 _86426 q p).
Proof. exact (MK_COMB (@lem3297881) (@lem3297880 _86426 q p)). Qed.
Lemma lem3297883 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term166 _86426 q p) = (term154 _86426 p q).
Proof. exact (eq_refl (term166 _86426 q p)). Qed.
Lemma lem3297884 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term167 _86426 q p) = (term155 _86426 p q).
Proof. exact (MK_COMB (@lem3297882 _86426 q p) (@lem3297883 _86426 p q)). Qed.
Lemma lem3297885 {_86426 : Type'} (q : _86426 -> Prop) : (term168 _86426 q) = (term157 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297884 _86426 p q)). Qed.
Lemma lem3297886 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297887 {_86426 : Type'} (q : _86426 -> Prop) : (term160 _86426 q) = (term159 _86426 q).
Proof. exact (MK_COMB (@lem3297886 _86426) (@lem3297885 _86426 q)). Qed.
Lemma lem3297888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297889 {_86426 : Type'} (q : _86426 -> Prop) : (term169 _86426 q) = (term170 _86426 q).
Proof. exact (MK_COMB (@lem3297888) (@lem3297887 _86426 q)). Qed.
Lemma lem3297890 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term164 _86426 q p) = (term34 _86426 q p).
Proof. exact (eq_refl (term164 _86426 q p)). Qed.
Lemma lem3297891 {_86426 : Type'} (q : _86426 -> Prop) : (term171 _86426 q) = (term162 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297890 _86426 q p)). Qed.
Lemma lem3297892 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297893 {_86426 : Type'} (q : _86426 -> Prop) : (term172 _86426 q) = (term173 _86426 q).
Proof. exact (MK_COMB (@lem3297892 _86426) (@lem3297891 _86426 q)). Qed.
Lemma lem3297894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297895 {_86426 : Type'} (q : _86426 -> Prop) : (term174 _86426 q) = (term175 _86426 q).
Proof. exact (MK_COMB (@lem3297894) (@lem3297893 _86426 q)). Qed.
Lemma lem3297896 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term166 _86426 q p) = (term154 _86426 p q).
Proof. exact (eq_refl (term166 _86426 q p)). Qed.
Lemma lem3297897 {_86426 : Type'} (q : _86426 -> Prop) : (term176 _86426 q) = (term163 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297896 _86426 p q)). Qed.
Lemma lem3297898 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297899 {_86426 : Type'} (q : _86426 -> Prop) : (term177 _86426 q) = (term178 _86426 q).
Proof. exact (MK_COMB (@lem3297898 _86426) (@lem3297897 _86426 q)). Qed.
Lemma lem3297900 {_86426 : Type'} (q : _86426 -> Prop) : (term161 _86426 q) = (term179 _86426 q).
Proof. exact (MK_COMB (@lem3297895 _86426 q) (@lem3297899 _86426 q)). Qed.
Lemma lem3297901 {_86426 : Type'} (q : _86426 -> Prop) : ((term160 _86426 q) = (term161 _86426 q)) = ((term159 _86426 q) = (term179 _86426 q)).
Proof. exact (MK_COMB (@lem3297889 _86426 q) (@lem3297900 _86426 q)). Qed.
Lemma lem3297902 {_86426 : Type'} (q : _86426 -> Prop) : (term159 _86426 q) = (term179 _86426 q).
Proof. exact (EQ_MP (@lem3297901 _86426 q) (@lem3297879 _86426 q)). Qed.
Lemma lem3297918 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3297919 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3297918 (_86426 -> Prop) P Q). Qed.
Lemma lem3297920 {_86426 : Type'} (q : _86426 -> Prop) : (term180 _86426 q) = (term181 _86426 q).
Proof. exact (@lem3297919 _86426 (term182 _86426 q) (term183 _86426 q)). Qed.
Lemma lem3297921 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term184 _86426 q p) = (term126 _86426 p q).
Proof. exact (eq_refl (term184 _86426 q p)). Qed.
Lemma lem3297922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297923 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term185 _86426 q p) = (term128 _86426 p q).
Proof. exact (MK_COMB (@lem3297922) (@lem3297921 _86426 p q)). Qed.
Lemma lem3297924 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term186 _86426 q p) = (term153 _86426 p q).
Proof. exact (eq_refl (term186 _86426 q p)). Qed.
Lemma lem3297925 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term187 _86426 q p) = (term154 _86426 p q).
Proof. exact (MK_COMB (@lem3297923 _86426 p q) (@lem3297924 _86426 p q)). Qed.
Lemma lem3297926 {_86426 : Type'} (q : _86426 -> Prop) : (term188 _86426 q) = (term163 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297925 _86426 p q)). Qed.
Lemma lem3297927 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297928 {_86426 : Type'} (q : _86426 -> Prop) : (term180 _86426 q) = (term178 _86426 q).
Proof. exact (MK_COMB (@lem3297927 _86426) (@lem3297926 _86426 q)). Qed.
Lemma lem3297929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297930 {_86426 : Type'} (q : _86426 -> Prop) : (term189 _86426 q) = (term190 _86426 q).
Proof. exact (MK_COMB (@lem3297929) (@lem3297928 _86426 q)). Qed.
Lemma lem3297931 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term184 _86426 q p) = (term126 _86426 p q).
Proof. exact (eq_refl (term184 _86426 q p)). Qed.
Lemma lem3297932 {_86426 : Type'} (q : _86426 -> Prop) : (term191 _86426 q) = (term182 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297931 _86426 p q)). Qed.
Lemma lem3297933 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297934 {_86426 : Type'} (q : _86426 -> Prop) : (term192 _86426 q) = (term193 _86426 q).
Proof. exact (MK_COMB (@lem3297933 _86426) (@lem3297932 _86426 q)). Qed.
Lemma lem3297935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297936 {_86426 : Type'} (q : _86426 -> Prop) : (term194 _86426 q) = (term195 _86426 q).
Proof. exact (MK_COMB (@lem3297935) (@lem3297934 _86426 q)). Qed.
Lemma lem3297937 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term186 _86426 q p) = (term153 _86426 p q).
Proof. exact (eq_refl (term186 _86426 q p)). Qed.
Lemma lem3297938 {_86426 : Type'} (q : _86426 -> Prop) : (term196 _86426 q) = (term183 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297937 _86426 p q)). Qed.
Lemma lem3297939 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297940 {_86426 : Type'} (q : _86426 -> Prop) : (term197 _86426 q) = (term198 _86426 q).
Proof. exact (MK_COMB (@lem3297939 _86426) (@lem3297938 _86426 q)). Qed.
Lemma lem3297941 {_86426 : Type'} (q : _86426 -> Prop) : (term181 _86426 q) = (term199 _86426 q).
Proof. exact (MK_COMB (@lem3297936 _86426 q) (@lem3297940 _86426 q)). Qed.
Lemma lem3297942 {_86426 : Type'} (q : _86426 -> Prop) : ((term180 _86426 q) = (term181 _86426 q)) = ((term178 _86426 q) = (term199 _86426 q)).
Proof. exact (MK_COMB (@lem3297930 _86426 q) (@lem3297941 _86426 q)). Qed.
Lemma lem3297943 {_86426 : Type'} (q : _86426 -> Prop) : (term178 _86426 q) = (term199 _86426 q).
Proof. exact (EQ_MP (@lem3297942 _86426 q) (@lem3297920 _86426 q)). Qed.
Lemma lem3297967 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3297968 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3297967 (_86426 -> Prop) P Q). Qed.
Lemma lem3297969 {_86426 : Type'} (q : _86426 -> Prop) : (term200 _86426 q) = (term201 _86426 q).
Proof. exact (@lem3297968 _86426 (term202 _86426 q) (term203 _86426 q)). Qed.
Lemma lem3297970 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term204 _86426 q p) = (term146 _86426 q p).
Proof. exact (eq_refl (term204 _86426 q p)). Qed.
Lemma lem3297971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297972 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term205 _86426 q p) = (term148 _86426 q p).
Proof. exact (MK_COMB (@lem3297971) (@lem3297970 _86426 q p)). Qed.
Lemma lem3297973 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term206 _86426 q p) = (term71 _86426 p q).
Proof. exact (eq_refl (term206 _86426 q p)). Qed.
Lemma lem3297974 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term207 _86426 q p) = (term153 _86426 p q).
Proof. exact (MK_COMB (@lem3297972 _86426 q p) (@lem3297973 _86426 p q)). Qed.
Lemma lem3297975 {_86426 : Type'} (q : _86426 -> Prop) : (term208 _86426 q) = (term183 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297974 _86426 p q)). Qed.
Lemma lem3297976 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297977 {_86426 : Type'} (q : _86426 -> Prop) : (term200 _86426 q) = (term198 _86426 q).
Proof. exact (MK_COMB (@lem3297976 _86426) (@lem3297975 _86426 q)). Qed.
Lemma lem3297978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3297979 {_86426 : Type'} (q : _86426 -> Prop) : (term209 _86426 q) = (term210 _86426 q).
Proof. exact (MK_COMB (@lem3297978) (@lem3297977 _86426 q)). Qed.
Lemma lem3297980 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term204 _86426 q p) = (term146 _86426 q p).
Proof. exact (eq_refl (term204 _86426 q p)). Qed.
Lemma lem3297981 {_86426 : Type'} (q : _86426 -> Prop) : (term211 _86426 q) = (term202 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297980 _86426 q p)). Qed.
Lemma lem3297982 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297983 {_86426 : Type'} (q : _86426 -> Prop) : (term212 _86426 q) = (term213 _86426 q).
Proof. exact (MK_COMB (@lem3297982 _86426) (@lem3297981 _86426 q)). Qed.
Lemma lem3297984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3297985 {_86426 : Type'} (q : _86426 -> Prop) : (term214 _86426 q) = (term215 _86426 q).
Proof. exact (MK_COMB (@lem3297984) (@lem3297983 _86426 q)). Qed.
Lemma lem3297986 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term206 _86426 q p) = (term71 _86426 p q).
Proof. exact (eq_refl (term206 _86426 q p)). Qed.
Lemma lem3297987 {_86426 : Type'} (q : _86426 -> Prop) : (term216 _86426 q) = (term203 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3297986 _86426 p q)). Qed.
Lemma lem3297988 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3297989 {_86426 : Type'} (q : _86426 -> Prop) : (term217 _86426 q) = (term218 _86426 q).
Proof. exact (MK_COMB (@lem3297988 _86426) (@lem3297987 _86426 q)). Qed.
Lemma lem3297990 {_86426 : Type'} (q : _86426 -> Prop) : (term201 _86426 q) = (term219 _86426 q).
Proof. exact (MK_COMB (@lem3297985 _86426 q) (@lem3297989 _86426 q)). Qed.
Lemma lem3297991 {_86426 : Type'} (q : _86426 -> Prop) : ((term200 _86426 q) = (term201 _86426 q)) = ((term198 _86426 q) = (term219 _86426 q)).
Proof. exact (MK_COMB (@lem3297979 _86426 q) (@lem3297990 _86426 q)). Qed.
Lemma lem3297992 {_86426 : Type'} (q : _86426 -> Prop) : (term198 _86426 q) = (term219 _86426 q).
Proof. exact (EQ_MP (@lem3297991 _86426 q) (@lem3297969 _86426 q)). Qed.
Lemma lem3298029 {_86426 : Type'} (q : _86426 -> Prop) : (term195 _86426 q) = (term195 _86426 q).
Proof. exact (eq_refl (term195 _86426 q)). Qed.
Lemma lem3298030 {_86426 : Type'} (q : _86426 -> Prop) : (term199 _86426 q) = (term220 _86426 q).
Proof. exact (MK_COMB (@lem3298029 _86426 q) (@lem3297992 _86426 q)). Qed.
Lemma lem3298033 {_86426 : Type'} (q : _86426 -> Prop) : (term178 _86426 q) = (term220 _86426 q).
Proof. exact (TRANS (@lem3297943 _86426 q) (@lem3298030 _86426 q)). Qed.
Lemma lem3298034 {_86426 : Type'} (q : _86426 -> Prop) : (term175 _86426 q) = (term175 _86426 q).
Proof. exact (eq_refl (term175 _86426 q)). Qed.
Lemma lem3298035 {_86426 : Type'} (q : _86426 -> Prop) : (term179 _86426 q) = (term221 _86426 q).
Proof. exact (MK_COMB (@lem3298034 _86426 q) (@lem3298033 _86426 q)). Qed.
Lemma lem3298038 {_86426 : Type'} (q : _86426 -> Prop) : (term159 _86426 q) = (term221 _86426 q).
Proof. exact (TRANS (@lem3297902 _86426 q) (@lem3298035 _86426 q)). Qed.
Lemma lem3298039 {_86426 : Type'} (q : _86426 -> Prop) : (term158 _86426 q) = (term221 _86426 q).
Proof. exact (TRANS (@lem3297875 _86426 q) (@lem3298038 _86426 q)). Qed.
Lemma lem3298040 {_86426 : Type'} : (term222 _86426) = (term223 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298039 _86426 q)). Qed.
Lemma lem3298041 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298042 {_86426 : Type'} : (term224 _86426) = (term225 _86426).
Proof. exact (MK_COMB (@lem3298041 _86426) (@lem3298040 _86426)). Qed.
Lemma lem3298044 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3298045 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3298044 (_86426 -> Prop) P Q). Qed.
Lemma lem3298046 {_86426 : Type'} : (term226 _86426) = (term227 _86426).
Proof. exact (@lem3298045 _86426 (term228 _86426) (term229 _86426)). Qed.
Lemma lem3298047 {_86426 : Type'} (q : _86426 -> Prop) : (term230 _86426 q) = (term173 _86426 q).
Proof. exact (eq_refl (term230 _86426 q)). Qed.
Lemma lem3298048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298049 {_86426 : Type'} (q : _86426 -> Prop) : (term231 _86426 q) = (term175 _86426 q).
Proof. exact (MK_COMB (@lem3298048) (@lem3298047 _86426 q)). Qed.
Lemma lem3298050 {_86426 : Type'} (q : _86426 -> Prop) : (term232 _86426 q) = (term220 _86426 q).
Proof. exact (eq_refl (term232 _86426 q)). Qed.
Lemma lem3298051 {_86426 : Type'} (q : _86426 -> Prop) : (term233 _86426 q) = (term221 _86426 q).
Proof. exact (MK_COMB (@lem3298049 _86426 q) (@lem3298050 _86426 q)). Qed.
Lemma lem3298052 {_86426 : Type'} : (term234 _86426) = (term223 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298051 _86426 q)). Qed.
Lemma lem3298053 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298054 {_86426 : Type'} : (term226 _86426) = (term225 _86426).
Proof. exact (MK_COMB (@lem3298053 _86426) (@lem3298052 _86426)). Qed.
Lemma lem3298055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3298056 {_86426 : Type'} : (term235 _86426) = (term236 _86426).
Proof. exact (MK_COMB (@lem3298055) (@lem3298054 _86426)). Qed.
Lemma lem3298057 {_86426 : Type'} (q : _86426 -> Prop) : (term230 _86426 q) = (term173 _86426 q).
Proof. exact (eq_refl (term230 _86426 q)). Qed.
Lemma lem3298058 {_86426 : Type'} : (term237 _86426) = (term228 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298057 _86426 q)). Qed.
Lemma lem3298059 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298060 {_86426 : Type'} : (term238 _86426) = (term239 _86426).
Proof. exact (MK_COMB (@lem3298059 _86426) (@lem3298058 _86426)). Qed.
Lemma lem3298061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298062 {_86426 : Type'} : (term240 _86426) = (term241 _86426).
Proof. exact (MK_COMB (@lem3298061) (@lem3298060 _86426)). Qed.
Lemma lem3298063 {_86426 : Type'} (q : _86426 -> Prop) : (term232 _86426 q) = (term220 _86426 q).
Proof. exact (eq_refl (term232 _86426 q)). Qed.
Lemma lem3298064 {_86426 : Type'} : (term242 _86426) = (term229 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298063 _86426 q)). Qed.
Lemma lem3298065 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298066 {_86426 : Type'} : (term243 _86426) = (term244 _86426).
Proof. exact (MK_COMB (@lem3298065 _86426) (@lem3298064 _86426)). Qed.
Lemma lem3298067 {_86426 : Type'} : (term227 _86426) = (term245 _86426).
Proof. exact (MK_COMB (@lem3298062 _86426) (@lem3298066 _86426)). Qed.
Lemma lem3298068 {_86426 : Type'} : ((term226 _86426) = (term227 _86426)) = ((term225 _86426) = (term245 _86426)).
Proof. exact (MK_COMB (@lem3298056 _86426) (@lem3298067 _86426)). Qed.
Lemma lem3298069 {_86426 : Type'} : (term225 _86426) = (term245 _86426).
Proof. exact (EQ_MP (@lem3298068 _86426) (@lem3298046 _86426)). Qed.
Lemma lem3298089 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3298090 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3298089 (_86426 -> Prop) P Q). Qed.
Lemma lem3298091 {_86426 : Type'} : (term246 _86426) = (term247 _86426).
Proof. exact (@lem3298090 _86426 (term248 _86426) (term249 _86426)). Qed.
Lemma lem3298092 {_86426 : Type'} (q : _86426 -> Prop) : (term250 _86426 q) = (term193 _86426 q).
Proof. exact (eq_refl (term250 _86426 q)). Qed.
Lemma lem3298093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298094 {_86426 : Type'} (q : _86426 -> Prop) : (term251 _86426 q) = (term195 _86426 q).
Proof. exact (MK_COMB (@lem3298093) (@lem3298092 _86426 q)). Qed.
Lemma lem3298095 {_86426 : Type'} (q : _86426 -> Prop) : (term252 _86426 q) = (term219 _86426 q).
Proof. exact (eq_refl (term252 _86426 q)). Qed.
Lemma lem3298096 {_86426 : Type'} (q : _86426 -> Prop) : (term253 _86426 q) = (term220 _86426 q).
Proof. exact (MK_COMB (@lem3298094 _86426 q) (@lem3298095 _86426 q)). Qed.
Lemma lem3298097 {_86426 : Type'} : (term254 _86426) = (term229 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298096 _86426 q)). Qed.
Lemma lem3298098 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298099 {_86426 : Type'} : (term246 _86426) = (term244 _86426).
Proof. exact (MK_COMB (@lem3298098 _86426) (@lem3298097 _86426)). Qed.
Lemma lem3298100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3298101 {_86426 : Type'} : (term255 _86426) = (term256 _86426).
Proof. exact (MK_COMB (@lem3298100) (@lem3298099 _86426)). Qed.
Lemma lem3298102 {_86426 : Type'} (q : _86426 -> Prop) : (term250 _86426 q) = (term193 _86426 q).
Proof. exact (eq_refl (term250 _86426 q)). Qed.
Lemma lem3298103 {_86426 : Type'} : (term257 _86426) = (term248 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298102 _86426 q)). Qed.
Lemma lem3298104 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298105 {_86426 : Type'} : (term258 _86426) = (term259 _86426).
Proof. exact (MK_COMB (@lem3298104 _86426) (@lem3298103 _86426)). Qed.
Lemma lem3298106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298107 {_86426 : Type'} : (term260 _86426) = (term261 _86426).
Proof. exact (MK_COMB (@lem3298106) (@lem3298105 _86426)). Qed.
Lemma lem3298108 {_86426 : Type'} (q : _86426 -> Prop) : (term252 _86426 q) = (term219 _86426 q).
Proof. exact (eq_refl (term252 _86426 q)). Qed.
Lemma lem3298109 {_86426 : Type'} : (term262 _86426) = (term249 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298108 _86426 q)). Qed.
Lemma lem3298110 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298111 {_86426 : Type'} : (term263 _86426) = (term264 _86426).
Proof. exact (MK_COMB (@lem3298110 _86426) (@lem3298109 _86426)). Qed.
Lemma lem3298112 {_86426 : Type'} : (term247 _86426) = (term265 _86426).
Proof. exact (MK_COMB (@lem3298107 _86426) (@lem3298111 _86426)). Qed.
Lemma lem3298113 {_86426 : Type'} : ((term246 _86426) = (term247 _86426)) = ((term244 _86426) = (term265 _86426)).
Proof. exact (MK_COMB (@lem3298101 _86426) (@lem3298112 _86426)). Qed.
Lemma lem3298114 {_86426 : Type'} : (term244 _86426) = (term265 _86426).
Proof. exact (EQ_MP (@lem3298113 _86426) (@lem3298091 _86426)). Qed.
Lemma lem3298142 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3298143 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term90 _86426 P Q) = (term91 _86426 P Q).
Proof. exact (@lem3298142 (_86426 -> Prop) P Q). Qed.
Lemma lem3298144 {_86426 : Type'} : (term266 _86426) = (term267 _86426).
Proof. exact (@lem3298143 _86426 (term268 _86426) (term269 _86426)). Qed.
Lemma lem3298145 {_86426 : Type'} (q : _86426 -> Prop) : (term270 _86426 q) = (term213 _86426 q).
Proof. exact (eq_refl (term270 _86426 q)). Qed.
Lemma lem3298146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298147 {_86426 : Type'} (q : _86426 -> Prop) : (term271 _86426 q) = (term215 _86426 q).
Proof. exact (MK_COMB (@lem3298146) (@lem3298145 _86426 q)). Qed.
Lemma lem3298148 {_86426 : Type'} (q : _86426 -> Prop) : (term272 _86426 q) = (term218 _86426 q).
Proof. exact (eq_refl (term272 _86426 q)). Qed.
Lemma lem3298149 {_86426 : Type'} (q : _86426 -> Prop) : (term273 _86426 q) = (term219 _86426 q).
Proof. exact (MK_COMB (@lem3298147 _86426 q) (@lem3298148 _86426 q)). Qed.
Lemma lem3298150 {_86426 : Type'} : (term274 _86426) = (term249 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298149 _86426 q)). Qed.
Lemma lem3298151 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298152 {_86426 : Type'} : (term266 _86426) = (term264 _86426).
Proof. exact (MK_COMB (@lem3298151 _86426) (@lem3298150 _86426)). Qed.
Lemma lem3298153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3298154 {_86426 : Type'} : (term275 _86426) = (term276 _86426).
Proof. exact (MK_COMB (@lem3298153) (@lem3298152 _86426)). Qed.
Lemma lem3298155 {_86426 : Type'} (q : _86426 -> Prop) : (term270 _86426 q) = (term213 _86426 q).
Proof. exact (eq_refl (term270 _86426 q)). Qed.
Lemma lem3298156 {_86426 : Type'} : (term277 _86426) = (term268 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298155 _86426 q)). Qed.
Lemma lem3298157 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298158 {_86426 : Type'} : (term278 _86426) = (term279 _86426).
Proof. exact (MK_COMB (@lem3298157 _86426) (@lem3298156 _86426)). Qed.
Lemma lem3298159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298160 {_86426 : Type'} : (term280 _86426) = (term281 _86426).
Proof. exact (MK_COMB (@lem3298159) (@lem3298158 _86426)). Qed.
Lemma lem3298161 {_86426 : Type'} (q : _86426 -> Prop) : (term272 _86426 q) = (term218 _86426 q).
Proof. exact (eq_refl (term272 _86426 q)). Qed.
Lemma lem3298162 {_86426 : Type'} : (term282 _86426) = (term269 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298161 _86426 q)). Qed.
Lemma lem3298163 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298164 {_86426 : Type'} : (term283 _86426) = (term284 _86426).
Proof. exact (MK_COMB (@lem3298163 _86426) (@lem3298162 _86426)). Qed.
Lemma lem3298165 {_86426 : Type'} : (term267 _86426) = (term285 _86426).
Proof. exact (MK_COMB (@lem3298160 _86426) (@lem3298164 _86426)). Qed.
Lemma lem3298166 {_86426 : Type'} : ((term266 _86426) = (term267 _86426)) = ((term264 _86426) = (term285 _86426)).
Proof. exact (MK_COMB (@lem3298154 _86426) (@lem3298165 _86426)). Qed.
Lemma lem3298167 {_86426 : Type'} : (term264 _86426) = (term285 _86426).
Proof. exact (EQ_MP (@lem3298166 _86426) (@lem3298144 _86426)). Qed.
Lemma lem3298212 {_86426 : Type'} : (term261 _86426) = (term261 _86426).
Proof. exact (eq_refl (term261 _86426)). Qed.
Lemma lem3298213 {_86426 : Type'} : (term265 _86426) = (term286 _86426).
Proof. exact (MK_COMB (@lem3298212 _86426) (@lem3298167 _86426)). Qed.
Lemma lem3298216 {_86426 : Type'} : (term244 _86426) = (term286 _86426).
Proof. exact (TRANS (@lem3298114 _86426) (@lem3298213 _86426)). Qed.
Lemma lem3298217 {_86426 : Type'} : (term241 _86426) = (term241 _86426).
Proof. exact (eq_refl (term241 _86426)). Qed.
Lemma lem3298218 {_86426 : Type'} : (term245 _86426) = (term287 _86426).
Proof. exact (MK_COMB (@lem3298217 _86426) (@lem3298216 _86426)). Qed.
Lemma lem3298221 {_86426 : Type'} : (term225 _86426) = (term287 _86426).
Proof. exact (TRANS (@lem3298069 _86426) (@lem3298218 _86426)). Qed.
Lemma lem3298226 {_86426 : Type'} : (term224 _86426) = (term287 _86426).
Proof. exact (TRANS (@lem3298042 _86426) (@lem3298221 _86426)). Qed.
Lemma lem3298243 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : ((term66 _86426 p q x) = (term29 _86426 p q x)) = ((term66 _86426 p q x) = (term29 _86426 p q x)).
Proof. exact (eq_refl ((term66 _86426 p q x) = (term29 _86426 p q x))). Qed.
Lemma lem3298244 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term70 _86426 p q) = (term70 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3298243 _86426 p q x)). Qed.
Lemma lem3298245 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3298246 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term71 _86426 p q) = (term71 _86426 p q).
Proof. exact (MK_COMB (@lem3298245 _86426) (@lem3298244 _86426 p q)). Qed.
Lemma lem3298247 {_86426 : Type'} (q : _86426 -> Prop) : (term203 _86426 q) = (term203 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298246 _86426 p q)). Qed.
Lemma lem3298248 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298249 {_86426 : Type'} (q : _86426 -> Prop) : (term218 _86426 q) = (term218 _86426 q).
Proof. exact (MK_COMB (@lem3298248 _86426) (@lem3298247 _86426 q)). Qed.
Lemma lem3298250 {_86426 : Type'} : (term269 _86426) = (term269 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298249 _86426 q)). Qed.
Lemma lem3298251 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298252 {_86426 : Type'} : (term284 _86426) = (term284 _86426).
Proof. exact (MK_COMB (@lem3298251 _86426) (@lem3298250 _86426)). Qed.
Lemma lem3298273 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : ((term45 _86426 p q r x) = (term45 _86426 q p r x)) = ((term45 _86426 p q r x) = (term45 _86426 q p r x)).
Proof. exact (eq_refl ((term45 _86426 p q r x) = (term45 _86426 q p r x))). Qed.
Lemma lem3298274 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term53 _86426 q p r) = (term53 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3298273 _86426 q p r x)). Qed.
Lemma lem3298275 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3298276 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term54 _86426 q p r) = (term54 _86426 q p r).
Proof. exact (MK_COMB (@lem3298275 _86426) (@lem3298274 _86426 q p r)). Qed.
Lemma lem3298277 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term135 _86426 q p) = (term135 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3298276 _86426 q p r)). Qed.
Lemma lem3298278 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298279 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term146 _86426 q p) = (term146 _86426 q p).
Proof. exact (MK_COMB (@lem3298278 _86426) (@lem3298277 _86426 q p)). Qed.
Lemma lem3298280 {_86426 : Type'} (q : _86426 -> Prop) : (term202 _86426 q) = (term202 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298279 _86426 q p)). Qed.
Lemma lem3298281 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298282 {_86426 : Type'} (q : _86426 -> Prop) : (term213 _86426 q) = (term213 _86426 q).
Proof. exact (MK_COMB (@lem3298281 _86426) (@lem3298280 _86426 q)). Qed.
Lemma lem3298283 {_86426 : Type'} : (term268 _86426) = (term268 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298282 _86426 q)). Qed.
Lemma lem3298284 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298285 {_86426 : Type'} : (term279 _86426) = (term279 _86426).
Proof. exact (MK_COMB (@lem3298284 _86426) (@lem3298283 _86426)). Qed.
Lemma lem3298286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298287 {_86426 : Type'} : (term281 _86426) = (term281 _86426).
Proof. exact (MK_COMB (@lem3298286) (@lem3298285 _86426)). Qed.
Lemma lem3298288 {_86426 : Type'} : (term285 _86426) = (term285 _86426).
Proof. exact (MK_COMB (@lem3298287 _86426) (@lem3298252 _86426)). Qed.
Lemma lem3298309 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : ((term40 _86426 p q r x) = (term45 _86426 p q r x)) = ((term40 _86426 p q r x) = (term45 _86426 p q r x)).
Proof. exact (eq_refl ((term40 _86426 p q r x) = (term45 _86426 p q r x))). Qed.
Lemma lem3298310 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term47 _86426 p q r) = (term47 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3298309 _86426 p q r x)). Qed.
Lemma lem3298311 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3298312 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term48 _86426 p q r) = (term48 _86426 p q r).
Proof. exact (MK_COMB (@lem3298311 _86426) (@lem3298310 _86426 p q r)). Qed.
Lemma lem3298313 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term115 _86426 p q) = (term115 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3298312 _86426 p q r)). Qed.
Lemma lem3298314 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298315 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term126 _86426 p q) = (term126 _86426 p q).
Proof. exact (MK_COMB (@lem3298314 _86426) (@lem3298313 _86426 p q)). Qed.
Lemma lem3298316 {_86426 : Type'} (q : _86426 -> Prop) : (term182 _86426 q) = (term182 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298315 _86426 p q)). Qed.
Lemma lem3298317 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298318 {_86426 : Type'} (q : _86426 -> Prop) : (term193 _86426 q) = (term193 _86426 q).
Proof. exact (MK_COMB (@lem3298317 _86426) (@lem3298316 _86426 q)). Qed.
Lemma lem3298319 {_86426 : Type'} : (term248 _86426) = (term248 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298318 _86426 q)). Qed.
Lemma lem3298320 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298321 {_86426 : Type'} : (term259 _86426) = (term259 _86426).
Proof. exact (MK_COMB (@lem3298320 _86426) (@lem3298319 _86426)). Qed.
Lemma lem3298322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298323 {_86426 : Type'} : (term261 _86426) = (term261 _86426).
Proof. exact (MK_COMB (@lem3298322) (@lem3298321 _86426)). Qed.
Lemma lem3298324 {_86426 : Type'} : (term286 _86426) = (term286 _86426).
Proof. exact (MK_COMB (@lem3298323 _86426) (@lem3298288 _86426)). Qed.
Lemma lem3298337 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : ((term29 _86426 p q x) = (term29 _86426 q p x)) = ((term29 _86426 p q x) = (term29 _86426 q p x)).
Proof. exact (eq_refl ((term29 _86426 p q x) = (term29 _86426 q p x))). Qed.
Lemma lem3298338 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term33 _86426 q p) = (term33 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3298337 _86426 q p x)). Qed.
Lemma lem3298339 {_86426 : Type'} : (@all _86426) = (@all _86426).
Proof. exact (eq_refl (@all _86426)). Qed.
Lemma lem3298340 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term34 _86426 q p) = (term34 _86426 q p).
Proof. exact (MK_COMB (@lem3298339 _86426) (@lem3298338 _86426 q p)). Qed.
Lemma lem3298341 {_86426 : Type'} (q : _86426 -> Prop) : (term162 _86426 q) = (term162 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298340 _86426 q p)). Qed.
Lemma lem3298342 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298343 {_86426 : Type'} (q : _86426 -> Prop) : (term173 _86426 q) = (term173 _86426 q).
Proof. exact (MK_COMB (@lem3298342 _86426) (@lem3298341 _86426 q)). Qed.
Lemma lem3298344 {_86426 : Type'} : (term228 _86426) = (term228 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298343 _86426 q)). Qed.
Lemma lem3298345 {_86426 : Type'} : (@all (_86426 -> Prop)) = (@all (_86426 -> Prop)).
Proof. exact (eq_refl (@all (_86426 -> Prop))). Qed.
Lemma lem3298346 {_86426 : Type'} : (term239 _86426) = (term239 _86426).
Proof. exact (MK_COMB (@lem3298345 _86426) (@lem3298344 _86426)). Qed.
Lemma lem3298347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298348 {_86426 : Type'} : (term241 _86426) = (term241 _86426).
Proof. exact (MK_COMB (@lem3298347) (@lem3298346 _86426)). Qed.
Lemma lem3298349 {_86426 : Type'} : (term287 _86426) = (term287 _86426).
Proof. exact (MK_COMB (@lem3298348 _86426) (@lem3298324 _86426)). Qed.
Lemma lem3298468 {_86426 : Type'} : (term224 _86426) = (term287 _86426).
Proof. exact (TRANS (@lem3298226 _86426) (@lem3298349 _86426)). Qed.
Lemma lem3298469 {_86426 : Type'} : (term287 _86426) = (term224 _86426).
Proof. exact (SYM (@lem3298468 _86426)). Qed.
Lemma lem3298471 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3298472 {_86426 : Type'} : (term287 _86426) = (term288 _86426).
Proof. exact (@lem3298471 (term287 _86426)). Qed.
Lemma lem3298473 {_86426 : Type'} : (term288 _86426) = (term287 _86426).
Proof. exact (SYM (@lem3298472 _86426)). Qed.
Lemma lem3298474 {_86426 : Type'} (h1 : term289 _86426) : term289 _86426.
Proof. exact (h1). Qed.
Lemma lem3298483 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term290 _86426 p q x) = (term291 _86426 p q x).
Proof. exact (@lem17160 (p x) (q x)). Qed.
Lemma lem3298495 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term290 _86426 q p x) = (term291 _86426 q p x).
Proof. exact (@lem17160 (q x) (p x)). Qed.
Lemma lem3298498 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term29 _86426 q p x) = (term29 _86426 q p x).
Proof. exact (eq_refl (term29 _86426 q p x)). Qed.
Lemma lem3298499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298500 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term292 _86426 p q x) = (term293 _86426 p q x).
Proof. exact (MK_COMB (@lem3298499) (@lem3298483 _86426 p q x)). Qed.
Lemma lem3298501 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term294 _86426 q p x) = (term295 _86426 q p x).
Proof. exact (MK_COMB (@lem3298500 _86426 p q x) (@lem3298498 _86426 q p x)). Qed.
Lemma lem3298503 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term296 _86426 p q x) = (term296 _86426 p q x).
Proof. exact (eq_refl (term296 _86426 p q x)). Qed.
Lemma lem3298504 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term297 _86426 q p x) = (term298 _86426 q p x).
Proof. exact (MK_COMB (@lem3298503 _86426 p q x) (@lem3298495 _86426 q p x)). Qed.
Lemma lem3298505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298506 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term299 _86426 q p x) = (term300 _86426 q p x).
Proof. exact (MK_COMB (@lem3298505) (@lem3298504 _86426 q p x)). Qed.
Lemma lem3298507 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term301 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (MK_COMB (@lem3298506 _86426 q p x) (@lem3298501 _86426 q p x)). Qed.
Lemma lem3298508 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term303 _86426 q p x) = (term301 _86426 q p x).
Proof. exact (@lem17646 (term29 _86426 p q x) (term29 _86426 q p x)). Qed.
Lemma lem3298509 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term303 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (TRANS (@lem3298508 _86426 q p x) (@lem3298507 _86426 q p x)). Qed.
Lemma lem3298510 {_86426 : Type'} (P : _86426 -> Prop) : (term304 _86426 P) = (term305 _86426 P).
Proof. exact (@lem18392 _86426 P). Qed.
Lemma lem3298511 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term306 _86426 q p) = (term307 _86426 q p).
Proof. exact (@lem3298510 _86426 (term33 _86426 q p)). Qed.
Lemma lem3298512 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term308 _86426 q p x) = ((term29 _86426 p q x) = (term29 _86426 q p x)).
Proof. exact (eq_refl (term308 _86426 q p x)). Qed.
Lemma lem3298513 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298514 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term309 _86426 q p x) = (term303 _86426 q p x).
Proof. exact (MK_COMB (@lem3298513) (@lem3298512 _86426 q p x)). Qed.
Lemma lem3298515 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term309 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (TRANS (@lem3298514 _86426 q p x) (@lem3298509 _86426 q p x)). Qed.
Lemma lem3298516 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term310 _86426 q p) = (term311 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3298515 _86426 q p x)). Qed.
Lemma lem3298517 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298518 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term307 _86426 q p) = (term312 _86426 q p).
Proof. exact (MK_COMB (@lem3298517 _86426) (@lem3298516 _86426 q p)). Qed.
Lemma lem3298519 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term306 _86426 q p) = (term312 _86426 q p).
Proof. exact (TRANS (@lem3298511 _86426 q p) (@lem3298518 _86426 q p)). Qed.
Lemma lem3298520 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298521 {_86426 : Type'} (q : _86426 -> Prop) : (term315 _86426 q) = (term316 _86426 q).
Proof. exact (@lem3298520 _86426 (term162 _86426 q)). Qed.
Lemma lem3298522 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term164 _86426 q p) = (term34 _86426 q p).
Proof. exact (eq_refl (term164 _86426 q p)). Qed.
Lemma lem3298523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298524 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term317 _86426 q p) = (term306 _86426 q p).
Proof. exact (MK_COMB (@lem3298523) (@lem3298522 _86426 q p)). Qed.
Lemma lem3298525 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term317 _86426 q p) = (term312 _86426 q p).
Proof. exact (TRANS (@lem3298524 _86426 q p) (@lem3298519 _86426 q p)). Qed.
Lemma lem3298526 {_86426 : Type'} (q : _86426 -> Prop) : (term318 _86426 q) = (term319 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298525 _86426 q p)). Qed.
Lemma lem3298527 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298528 {_86426 : Type'} (q : _86426 -> Prop) : (term316 _86426 q) = (term320 _86426 q).
Proof. exact (MK_COMB (@lem3298527 _86426) (@lem3298526 _86426 q)). Qed.
Lemma lem3298529 {_86426 : Type'} (q : _86426 -> Prop) : (term315 _86426 q) = (term320 _86426 q).
Proof. exact (TRANS (@lem3298521 _86426 q) (@lem3298528 _86426 q)). Qed.
Lemma lem3298530 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298531 {_86426 : Type'} : (term321 _86426) = (term322 _86426).
Proof. exact (@lem3298530 _86426 (term228 _86426)). Qed.
Lemma lem3298532 {_86426 : Type'} (q : _86426 -> Prop) : (term230 _86426 q) = (term173 _86426 q).
Proof. exact (eq_refl (term230 _86426 q)). Qed.
Lemma lem3298533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298534 {_86426 : Type'} (q : _86426 -> Prop) : (term323 _86426 q) = (term315 _86426 q).
Proof. exact (MK_COMB (@lem3298533) (@lem3298532 _86426 q)). Qed.
Lemma lem3298535 {_86426 : Type'} (q : _86426 -> Prop) : (term323 _86426 q) = (term320 _86426 q).
Proof. exact (TRANS (@lem3298534 _86426 q) (@lem3298529 _86426 q)). Qed.
Lemma lem3298536 {_86426 : Type'} : (term324 _86426) = (term325 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298535 _86426 q)). Qed.
Lemma lem3298537 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298538 {_86426 : Type'} : (term322 _86426) = (term326 _86426).
Proof. exact (MK_COMB (@lem3298537 _86426) (@lem3298536 _86426)). Qed.
Lemma lem3298539 {_86426 : Type'} : (term321 _86426) = (term326 _86426).
Proof. exact (TRANS (@lem3298531 _86426) (@lem3298538 _86426)). Qed.
Lemma lem3298548 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term290 _86426 p q x) = (term291 _86426 p q x).
Proof. exact (@lem17160 (p x) (q x)). Qed.
Lemma lem3298552 {_86426 : Type'} (r : _86426 -> Prop) (x : _86426) : (term327 _86426 r x) = (term327 _86426 r x).
Proof. exact (eq_refl (term327 _86426 r x)). Qed.
Lemma lem3298554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298555 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term292 _86426 p q x) = (term293 _86426 p q x).
Proof. exact (MK_COMB (@lem3298554) (@lem3298548 _86426 p q x)). Qed.
Lemma lem3298556 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term328 _86426 p q r x) = (term329 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298555 _86426 p q x) (@lem3298552 _86426 r x)). Qed.
Lemma lem3298557 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term330 _86426 p q r x) = (term328 _86426 p q r x).
Proof. exact (@lem17160 (term29 _86426 p q x) (r x)). Qed.
Lemma lem3298558 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term330 _86426 p q r x) = (term329 _86426 p q r x).
Proof. exact (TRANS (@lem3298557 _86426 p q r x) (@lem3298556 _86426 p q r x)). Qed.
Lemma lem3298572 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term290 _86426 q r x) = (term291 _86426 q r x).
Proof. exact (@lem17160 (q x) (r x)). Qed.
Lemma lem3298577 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term331 _86426 p x) = (term331 _86426 p x).
Proof. exact (eq_refl (term331 _86426 p x)). Qed.
Lemma lem3298578 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term332 _86426 p q r x) = (term333 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298577 _86426 p x) (@lem3298572 _86426 q r x)). Qed.
Lemma lem3298579 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term334 _86426 p q r x) = (term332 _86426 p q r x).
Proof. exact (@lem17160 (p x) (term29 _86426 q r x)). Qed.
Lemma lem3298580 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term334 _86426 p q r x) = (term333 _86426 p q r x).
Proof. exact (TRANS (@lem3298579 _86426 p q r x) (@lem3298578 _86426 p q r x)). Qed.
Lemma lem3298583 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term45 _86426 p q r x) = (term45 _86426 p q r x).
Proof. exact (eq_refl (term45 _86426 p q r x)). Qed.
Lemma lem3298584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298585 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term335 _86426 p q r x) = (term336 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298584) (@lem3298558 _86426 p q r x)). Qed.
Lemma lem3298586 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term337 _86426 p q r x) = (term338 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298585 _86426 p q r x) (@lem3298583 _86426 p q r x)). Qed.
Lemma lem3298588 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term339 _86426 p q r x) = (term339 _86426 p q r x).
Proof. exact (eq_refl (term339 _86426 p q r x)). Qed.
Lemma lem3298589 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term340 _86426 p q r x) = (term341 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298588 _86426 p q r x) (@lem3298580 _86426 p q r x)). Qed.
Lemma lem3298590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298591 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term342 _86426 p q r x) = (term343 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298590) (@lem3298589 _86426 p q r x)). Qed.
Lemma lem3298592 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term344 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298591 _86426 p q r x) (@lem3298586 _86426 p q r x)). Qed.
Lemma lem3298593 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term346 _86426 p q r x) = (term344 _86426 p q r x).
Proof. exact (@lem17646 (term40 _86426 p q r x) (term45 _86426 p q r x)). Qed.
Lemma lem3298594 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term346 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (TRANS (@lem3298593 _86426 p q r x) (@lem3298592 _86426 p q r x)). Qed.
Lemma lem3298595 {_86426 : Type'} (P : _86426 -> Prop) : (term304 _86426 P) = (term305 _86426 P).
Proof. exact (@lem18392 _86426 P). Qed.
Lemma lem3298596 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term347 _86426 p q r) = (term348 _86426 p q r).
Proof. exact (@lem3298595 _86426 (term47 _86426 p q r)). Qed.
Lemma lem3298597 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term349 _86426 p q r x) = ((term40 _86426 p q r x) = (term45 _86426 p q r x)).
Proof. exact (eq_refl (term349 _86426 p q r x)). Qed.
Lemma lem3298598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298599 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term350 _86426 p q r x) = (term346 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298598) (@lem3298597 _86426 p q r x)). Qed.
Lemma lem3298600 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term350 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (TRANS (@lem3298599 _86426 p q r x) (@lem3298594 _86426 p q r x)). Qed.
Lemma lem3298601 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term351 _86426 p q r) = (term352 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3298600 _86426 p q r x)). Qed.
Lemma lem3298602 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298603 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term348 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (MK_COMB (@lem3298602 _86426) (@lem3298601 _86426 p q r)). Qed.
Lemma lem3298604 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term347 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (TRANS (@lem3298596 _86426 p q r) (@lem3298603 _86426 p q r)). Qed.
Lemma lem3298605 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298606 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term354 _86426 p q) = (term355 _86426 p q).
Proof. exact (@lem3298605 _86426 (term115 _86426 p q)). Qed.
Lemma lem3298607 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term117 _86426 p q r) = (term48 _86426 p q r).
Proof. exact (eq_refl (term117 _86426 p q r)). Qed.
Lemma lem3298608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298609 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term356 _86426 p q r) = (term347 _86426 p q r).
Proof. exact (MK_COMB (@lem3298608) (@lem3298607 _86426 p q r)). Qed.
Lemma lem3298610 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term356 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (TRANS (@lem3298609 _86426 p q r) (@lem3298604 _86426 p q r)). Qed.
Lemma lem3298611 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term357 _86426 p q) = (term358 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3298610 _86426 p q r)). Qed.
Lemma lem3298612 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298613 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term355 _86426 p q) = (term359 _86426 p q).
Proof. exact (MK_COMB (@lem3298612 _86426) (@lem3298611 _86426 p q)). Qed.
Lemma lem3298614 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term354 _86426 p q) = (term359 _86426 p q).
Proof. exact (TRANS (@lem3298606 _86426 p q) (@lem3298613 _86426 p q)). Qed.
Lemma lem3298615 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298616 {_86426 : Type'} (q : _86426 -> Prop) : (term360 _86426 q) = (term361 _86426 q).
Proof. exact (@lem3298615 _86426 (term182 _86426 q)). Qed.
Lemma lem3298617 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term184 _86426 q p) = (term126 _86426 p q).
Proof. exact (eq_refl (term184 _86426 q p)). Qed.
Lemma lem3298618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298619 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term362 _86426 q p) = (term354 _86426 p q).
Proof. exact (MK_COMB (@lem3298618) (@lem3298617 _86426 p q)). Qed.
Lemma lem3298620 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term362 _86426 q p) = (term359 _86426 p q).
Proof. exact (TRANS (@lem3298619 _86426 p q) (@lem3298614 _86426 p q)). Qed.
Lemma lem3298621 {_86426 : Type'} (q : _86426 -> Prop) : (term363 _86426 q) = (term364 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298620 _86426 p q)). Qed.
Lemma lem3298622 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298623 {_86426 : Type'} (q : _86426 -> Prop) : (term361 _86426 q) = (term365 _86426 q).
Proof. exact (MK_COMB (@lem3298622 _86426) (@lem3298621 _86426 q)). Qed.
Lemma lem3298624 {_86426 : Type'} (q : _86426 -> Prop) : (term360 _86426 q) = (term365 _86426 q).
Proof. exact (TRANS (@lem3298616 _86426 q) (@lem3298623 _86426 q)). Qed.
Lemma lem3298625 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298626 {_86426 : Type'} : (term366 _86426) = (term367 _86426).
Proof. exact (@lem3298625 _86426 (term248 _86426)). Qed.
Lemma lem3298627 {_86426 : Type'} (q : _86426 -> Prop) : (term250 _86426 q) = (term193 _86426 q).
Proof. exact (eq_refl (term250 _86426 q)). Qed.
Lemma lem3298628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298629 {_86426 : Type'} (q : _86426 -> Prop) : (term368 _86426 q) = (term360 _86426 q).
Proof. exact (MK_COMB (@lem3298628) (@lem3298627 _86426 q)). Qed.
Lemma lem3298630 {_86426 : Type'} (q : _86426 -> Prop) : (term368 _86426 q) = (term365 _86426 q).
Proof. exact (TRANS (@lem3298629 _86426 q) (@lem3298624 _86426 q)). Qed.
Lemma lem3298631 {_86426 : Type'} : (term369 _86426) = (term370 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298630 _86426 q)). Qed.
Lemma lem3298632 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298633 {_86426 : Type'} : (term367 _86426) = (term371 _86426).
Proof. exact (MK_COMB (@lem3298632 _86426) (@lem3298631 _86426)). Qed.
Lemma lem3298634 {_86426 : Type'} : (term366 _86426) = (term371 _86426).
Proof. exact (TRANS (@lem3298626 _86426) (@lem3298633 _86426)). Qed.
Lemma lem3298645 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term290 _86426 q r x) = (term291 _86426 q r x).
Proof. exact (@lem17160 (q x) (r x)). Qed.
Lemma lem3298650 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term331 _86426 p x) = (term331 _86426 p x).
Proof. exact (eq_refl (term331 _86426 p x)). Qed.
Lemma lem3298651 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term332 _86426 p q r x) = (term333 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298650 _86426 p x) (@lem3298645 _86426 q r x)). Qed.
Lemma lem3298652 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term334 _86426 p q r x) = (term332 _86426 p q r x).
Proof. exact (@lem17160 (p x) (term29 _86426 q r x)). Qed.
Lemma lem3298653 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term334 _86426 p q r x) = (term333 _86426 p q r x).
Proof. exact (TRANS (@lem3298652 _86426 p q r x) (@lem3298651 _86426 p q r x)). Qed.
Lemma lem3298667 {_86426 : Type'} (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term290 _86426 p r x) = (term291 _86426 p r x).
Proof. exact (@lem17160 (p x) (r x)). Qed.
Lemma lem3298672 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term331 _86426 q x) = (term331 _86426 q x).
Proof. exact (eq_refl (term331 _86426 q x)). Qed.
Lemma lem3298673 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term332 _86426 q p r x) = (term333 _86426 q p r x).
Proof. exact (MK_COMB (@lem3298672 _86426 q x) (@lem3298667 _86426 p r x)). Qed.
Lemma lem3298674 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term334 _86426 q p r x) = (term332 _86426 q p r x).
Proof. exact (@lem17160 (q x) (term29 _86426 p r x)). Qed.
Lemma lem3298675 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term334 _86426 q p r x) = (term333 _86426 q p r x).
Proof. exact (TRANS (@lem3298674 _86426 q p r x) (@lem3298673 _86426 q p r x)). Qed.
Lemma lem3298678 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term45 _86426 q p r x) = (term45 _86426 q p r x).
Proof. exact (eq_refl (term45 _86426 q p r x)). Qed.
Lemma lem3298679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298680 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term372 _86426 p q r x) = (term373 _86426 p q r x).
Proof. exact (MK_COMB (@lem3298679) (@lem3298653 _86426 p q r x)). Qed.
Lemma lem3298681 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term374 _86426 q p r x) = (term375 _86426 q p r x).
Proof. exact (MK_COMB (@lem3298680 _86426 p q r x) (@lem3298678 _86426 q p r x)). Qed.
Lemma lem3298683 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term376 _86426 p q r x) = (term376 _86426 p q r x).
Proof. exact (eq_refl (term376 _86426 p q r x)). Qed.
Lemma lem3298684 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term377 _86426 q p r x) = (term378 _86426 q p r x).
Proof. exact (MK_COMB (@lem3298683 _86426 p q r x) (@lem3298675 _86426 q p r x)). Qed.
Lemma lem3298685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298686 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term379 _86426 q p r x) = (term380 _86426 q p r x).
Proof. exact (MK_COMB (@lem3298685) (@lem3298684 _86426 q p r x)). Qed.
Lemma lem3298687 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term381 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (MK_COMB (@lem3298686 _86426 q p r x) (@lem3298681 _86426 q p r x)). Qed.
Lemma lem3298688 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term383 _86426 q p r x) = (term381 _86426 q p r x).
Proof. exact (@lem17646 (term45 _86426 p q r x) (term45 _86426 q p r x)). Qed.
Lemma lem3298689 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term383 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (TRANS (@lem3298688 _86426 q p r x) (@lem3298687 _86426 q p r x)). Qed.
Lemma lem3298690 {_86426 : Type'} (P : _86426 -> Prop) : (term304 _86426 P) = (term305 _86426 P).
Proof. exact (@lem18392 _86426 P). Qed.
Lemma lem3298691 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term384 _86426 q p r) = (term385 _86426 q p r).
Proof. exact (@lem3298690 _86426 (term53 _86426 q p r)). Qed.
Lemma lem3298692 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term386 _86426 q p r x) = ((term45 _86426 p q r x) = (term45 _86426 q p r x)).
Proof. exact (eq_refl (term386 _86426 q p r x)). Qed.
Lemma lem3298693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298694 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term387 _86426 q p r x) = (term383 _86426 q p r x).
Proof. exact (MK_COMB (@lem3298693) (@lem3298692 _86426 q p r x)). Qed.
Lemma lem3298695 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term387 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (TRANS (@lem3298694 _86426 q p r x) (@lem3298689 _86426 q p r x)). Qed.
Lemma lem3298696 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term388 _86426 q p r) = (term389 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3298695 _86426 q p r x)). Qed.
Lemma lem3298697 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298698 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term385 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (MK_COMB (@lem3298697 _86426) (@lem3298696 _86426 q p r)). Qed.
Lemma lem3298699 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term384 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (TRANS (@lem3298691 _86426 q p r) (@lem3298698 _86426 q p r)). Qed.
Lemma lem3298700 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298701 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term391 _86426 q p) = (term392 _86426 q p).
Proof. exact (@lem3298700 _86426 (term135 _86426 q p)). Qed.
Lemma lem3298702 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term137 _86426 q p r) = (term54 _86426 q p r).
Proof. exact (eq_refl (term137 _86426 q p r)). Qed.
Lemma lem3298703 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298704 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term393 _86426 q p r) = (term384 _86426 q p r).
Proof. exact (MK_COMB (@lem3298703) (@lem3298702 _86426 q p r)). Qed.
Lemma lem3298705 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term393 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (TRANS (@lem3298704 _86426 q p r) (@lem3298699 _86426 q p r)). Qed.
Lemma lem3298706 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term394 _86426 q p) = (term395 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3298705 _86426 q p r)). Qed.
Lemma lem3298707 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298708 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term392 _86426 q p) = (term396 _86426 q p).
Proof. exact (MK_COMB (@lem3298707 _86426) (@lem3298706 _86426 q p)). Qed.
Lemma lem3298709 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term391 _86426 q p) = (term396 _86426 q p).
Proof. exact (TRANS (@lem3298701 _86426 q p) (@lem3298708 _86426 q p)). Qed.
Lemma lem3298710 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298711 {_86426 : Type'} (q : _86426 -> Prop) : (term397 _86426 q) = (term398 _86426 q).
Proof. exact (@lem3298710 _86426 (term202 _86426 q)). Qed.
Lemma lem3298712 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term204 _86426 q p) = (term146 _86426 q p).
Proof. exact (eq_refl (term204 _86426 q p)). Qed.
Lemma lem3298713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298714 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term399 _86426 q p) = (term391 _86426 q p).
Proof. exact (MK_COMB (@lem3298713) (@lem3298712 _86426 q p)). Qed.
Lemma lem3298715 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term399 _86426 q p) = (term396 _86426 q p).
Proof. exact (TRANS (@lem3298714 _86426 q p) (@lem3298709 _86426 q p)). Qed.
Lemma lem3298716 {_86426 : Type'} (q : _86426 -> Prop) : (term400 _86426 q) = (term401 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298715 _86426 q p)). Qed.
Lemma lem3298717 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298718 {_86426 : Type'} (q : _86426 -> Prop) : (term398 _86426 q) = (term402 _86426 q).
Proof. exact (MK_COMB (@lem3298717 _86426) (@lem3298716 _86426 q)). Qed.
Lemma lem3298719 {_86426 : Type'} (q : _86426 -> Prop) : (term397 _86426 q) = (term402 _86426 q).
Proof. exact (TRANS (@lem3298711 _86426 q) (@lem3298718 _86426 q)). Qed.
Lemma lem3298720 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298721 {_86426 : Type'} : (term403 _86426) = (term404 _86426).
Proof. exact (@lem3298720 _86426 (term268 _86426)). Qed.
Lemma lem3298722 {_86426 : Type'} (q : _86426 -> Prop) : (term270 _86426 q) = (term213 _86426 q).
Proof. exact (eq_refl (term270 _86426 q)). Qed.
Lemma lem3298723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298724 {_86426 : Type'} (q : _86426 -> Prop) : (term405 _86426 q) = (term397 _86426 q).
Proof. exact (MK_COMB (@lem3298723) (@lem3298722 _86426 q)). Qed.
Lemma lem3298725 {_86426 : Type'} (q : _86426 -> Prop) : (term405 _86426 q) = (term402 _86426 q).
Proof. exact (TRANS (@lem3298724 _86426 q) (@lem3298719 _86426 q)). Qed.
Lemma lem3298726 {_86426 : Type'} : (term406 _86426) = (term407 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298725 _86426 q)). Qed.
Lemma lem3298727 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298728 {_86426 : Type'} : (term404 _86426) = (term408 _86426).
Proof. exact (MK_COMB (@lem3298727 _86426) (@lem3298726 _86426)). Qed.
Lemma lem3298729 {_86426 : Type'} : (term403 _86426) = (term408 _86426).
Proof. exact (TRANS (@lem3298721 _86426) (@lem3298728 _86426)). Qed.
Lemma lem3298740 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term290 _86426 p q x) = (term291 _86426 p q x).
Proof. exact (@lem17160 (p x) (q x)). Qed.
Lemma lem3298745 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term331 _86426 p x) = (term331 _86426 p x).
Proof. exact (eq_refl (term331 _86426 p x)). Qed.
Lemma lem3298746 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term409 _86426 p q x) = (term410 _86426 p q x).
Proof. exact (MK_COMB (@lem3298745 _86426 p x) (@lem3298740 _86426 p q x)). Qed.
Lemma lem3298747 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term411 _86426 p q x) = (term409 _86426 p q x).
Proof. exact (@lem17160 (p x) (term29 _86426 p q x)). Qed.
Lemma lem3298748 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term411 _86426 p q x) = (term410 _86426 p q x).
Proof. exact (TRANS (@lem3298747 _86426 p q x) (@lem3298746 _86426 p q x)). Qed.
Lemma lem3298760 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term290 _86426 p q x) = (term291 _86426 p q x).
Proof. exact (@lem17160 (p x) (q x)). Qed.
Lemma lem3298763 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term29 _86426 p q x) = (term29 _86426 p q x).
Proof. exact (eq_refl (term29 _86426 p q x)). Qed.
Lemma lem3298764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3298765 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term412 _86426 p q x) = (term413 _86426 p q x).
Proof. exact (MK_COMB (@lem3298764) (@lem3298748 _86426 p q x)). Qed.
Lemma lem3298766 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term414 _86426 p q x) = (term415 _86426 p q x).
Proof. exact (MK_COMB (@lem3298765 _86426 p q x) (@lem3298763 _86426 p q x)). Qed.
Lemma lem3298768 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term416 _86426 p q x) = (term416 _86426 p q x).
Proof. exact (eq_refl (term416 _86426 p q x)). Qed.
Lemma lem3298769 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term417 _86426 p q x) = (term418 _86426 p q x).
Proof. exact (MK_COMB (@lem3298768 _86426 p q x) (@lem3298760 _86426 p q x)). Qed.
Lemma lem3298770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298771 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term419 _86426 p q x) = (term420 _86426 p q x).
Proof. exact (MK_COMB (@lem3298770) (@lem3298769 _86426 p q x)). Qed.
Lemma lem3298772 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term421 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (MK_COMB (@lem3298771 _86426 p q x) (@lem3298766 _86426 p q x)). Qed.
Lemma lem3298773 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term423 _86426 p q x) = (term421 _86426 p q x).
Proof. exact (@lem17646 (term66 _86426 p q x) (term29 _86426 p q x)). Qed.
Lemma lem3298774 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term423 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (TRANS (@lem3298773 _86426 p q x) (@lem3298772 _86426 p q x)). Qed.
Lemma lem3298775 {_86426 : Type'} (P : _86426 -> Prop) : (term304 _86426 P) = (term305 _86426 P).
Proof. exact (@lem18392 _86426 P). Qed.
Lemma lem3298776 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term424 _86426 p q) = (term425 _86426 p q).
Proof. exact (@lem3298775 _86426 (term70 _86426 p q)). Qed.
Lemma lem3298777 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term426 _86426 p q x) = ((term66 _86426 p q x) = (term29 _86426 p q x)).
Proof. exact (eq_refl (term426 _86426 p q x)). Qed.
Lemma lem3298778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298779 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term427 _86426 p q x) = (term423 _86426 p q x).
Proof. exact (MK_COMB (@lem3298778) (@lem3298777 _86426 p q x)). Qed.
Lemma lem3298780 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term427 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (TRANS (@lem3298779 _86426 p q x) (@lem3298774 _86426 p q x)). Qed.
Lemma lem3298781 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term428 _86426 p q) = (term429 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3298780 _86426 p q x)). Qed.
Lemma lem3298782 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298783 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term425 _86426 p q) = (term430 _86426 p q).
Proof. exact (MK_COMB (@lem3298782 _86426) (@lem3298781 _86426 p q)). Qed.
Lemma lem3298784 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term424 _86426 p q) = (term430 _86426 p q).
Proof. exact (TRANS (@lem3298776 _86426 p q) (@lem3298783 _86426 p q)). Qed.
Lemma lem3298785 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298786 {_86426 : Type'} (q : _86426 -> Prop) : (term431 _86426 q) = (term432 _86426 q).
Proof. exact (@lem3298785 _86426 (term203 _86426 q)). Qed.
Lemma lem3298787 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term206 _86426 q p) = (term71 _86426 p q).
Proof. exact (eq_refl (term206 _86426 q p)). Qed.
Lemma lem3298788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298789 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term433 _86426 q p) = (term424 _86426 p q).
Proof. exact (MK_COMB (@lem3298788) (@lem3298787 _86426 p q)). Qed.
Lemma lem3298790 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term433 _86426 q p) = (term430 _86426 p q).
Proof. exact (TRANS (@lem3298789 _86426 p q) (@lem3298784 _86426 p q)). Qed.
Lemma lem3298791 {_86426 : Type'} (q : _86426 -> Prop) : (term434 _86426 q) = (term435 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298790 _86426 p q)). Qed.
Lemma lem3298792 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298793 {_86426 : Type'} (q : _86426 -> Prop) : (term432 _86426 q) = (term436 _86426 q).
Proof. exact (MK_COMB (@lem3298792 _86426) (@lem3298791 _86426 q)). Qed.
Lemma lem3298794 {_86426 : Type'} (q : _86426 -> Prop) : (term431 _86426 q) = (term436 _86426 q).
Proof. exact (TRANS (@lem3298786 _86426 q) (@lem3298793 _86426 q)). Qed.
Lemma lem3298795 {_86426 : Type'} (P : type686 _86426) : (term313 _86426 P) = (term314 _86426 P).
Proof. exact (@lem18392 (_86426 -> Prop) P). Qed.
Lemma lem3298796 {_86426 : Type'} : (term437 _86426) = (term438 _86426).
Proof. exact (@lem3298795 _86426 (term269 _86426)). Qed.
Lemma lem3298797 {_86426 : Type'} (q : _86426 -> Prop) : (term272 _86426 q) = (term218 _86426 q).
Proof. exact (eq_refl (term272 _86426 q)). Qed.
Lemma lem3298798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3298799 {_86426 : Type'} (q : _86426 -> Prop) : (term439 _86426 q) = (term431 _86426 q).
Proof. exact (MK_COMB (@lem3298798) (@lem3298797 _86426 q)). Qed.
Lemma lem3298800 {_86426 : Type'} (q : _86426 -> Prop) : (term439 _86426 q) = (term436 _86426 q).
Proof. exact (TRANS (@lem3298799 _86426 q) (@lem3298794 _86426 q)). Qed.
Lemma lem3298801 {_86426 : Type'} : (term440 _86426) = (term441 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3298800 _86426 q)). Qed.
Lemma lem3298802 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298803 {_86426 : Type'} : (term438 _86426) = (term442 _86426).
Proof. exact (MK_COMB (@lem3298802 _86426) (@lem3298801 _86426)). Qed.
Lemma lem3298804 {_86426 : Type'} : (term437 _86426) = (term442 _86426).
Proof. exact (TRANS (@lem3298796 _86426) (@lem3298803 _86426)). Qed.
Lemma lem3298805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298806 {_86426 : Type'} : (term443 _86426) = (term444 _86426).
Proof. exact (MK_COMB (@lem3298805) (@lem3298729 _86426)). Qed.
Lemma lem3298807 {_86426 : Type'} : (term445 _86426) = (term446 _86426).
Proof. exact (MK_COMB (@lem3298806 _86426) (@lem3298804 _86426)). Qed.
Lemma lem3298808 {_86426 : Type'} : (term447 _86426) = (term445 _86426).
Proof. exact (@lem17045 (term279 _86426) (term284 _86426)). Qed.
Lemma lem3298809 {_86426 : Type'} : (term447 _86426) = (term446 _86426).
Proof. exact (TRANS (@lem3298808 _86426) (@lem3298807 _86426)). Qed.
Lemma lem3298810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298811 {_86426 : Type'} : (term448 _86426) = (term449 _86426).
Proof. exact (MK_COMB (@lem3298810) (@lem3298634 _86426)). Qed.
Lemma lem3298812 {_86426 : Type'} : (term450 _86426) = (term451 _86426).
Proof. exact (MK_COMB (@lem3298811 _86426) (@lem3298809 _86426)). Qed.
Lemma lem3298813 {_86426 : Type'} : (term452 _86426) = (term450 _86426).
Proof. exact (@lem17045 (term259 _86426) (term285 _86426)). Qed.
Lemma lem3298814 {_86426 : Type'} : (term452 _86426) = (term451 _86426).
Proof. exact (TRANS (@lem3298813 _86426) (@lem3298812 _86426)). Qed.
Lemma lem3298815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298816 {_86426 : Type'} : (term453 _86426) = (term454 _86426).
Proof. exact (MK_COMB (@lem3298815) (@lem3298539 _86426)). Qed.
Lemma lem3298817 {_86426 : Type'} : (term455 _86426) = (term456 _86426).
Proof. exact (MK_COMB (@lem3298816 _86426) (@lem3298814 _86426)). Qed.
Lemma lem3298818 {_86426 : Type'} : (term289 _86426) = (term455 _86426).
Proof. exact (@lem17045 (term239 _86426) (term286 _86426)). Qed.
Lemma lem3298819 {_86426 : Type'} : (term289 _86426) = (term456 _86426).
Proof. exact (TRANS (@lem3298818 _86426) (@lem3298817 _86426)). Qed.
Lemma lem3298829 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3298830 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term457 _86426 P Q) = (term458 _86426 P Q).
Proof. exact (@lem3298829 _86426 P Q). Qed.
Lemma lem3298831 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term459 _86426 q p) = (term460 _86426 q p).
Proof. exact (@lem3298830 _86426 (term461 _86426 q p) (term462 _86426 q p)). Qed.
Lemma lem3298832 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term463 _86426 q p x) = (term298 _86426 q p x).
Proof. exact (eq_refl (term463 _86426 q p x)). Qed.
Lemma lem3298833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298834 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term464 _86426 q p x) = (term300 _86426 q p x).
Proof. exact (MK_COMB (@lem3298833) (@lem3298832 _86426 q p x)). Qed.
Lemma lem3298835 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term465 _86426 q p x) = (term295 _86426 q p x).
Proof. exact (eq_refl (term465 _86426 q p x)). Qed.
Lemma lem3298836 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term466 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (MK_COMB (@lem3298834 _86426 q p x) (@lem3298835 _86426 q p x)). Qed.
Lemma lem3298837 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term467 _86426 q p) = (term311 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3298836 _86426 q p x)). Qed.
Lemma lem3298838 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298839 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term459 _86426 q p) = (term312 _86426 q p).
Proof. exact (MK_COMB (@lem3298838 _86426) (@lem3298837 _86426 q p)). Qed.
Lemma lem3298840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3298841 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term468 _86426 q p) = (term469 _86426 q p).
Proof. exact (MK_COMB (@lem3298840) (@lem3298839 _86426 q p)). Qed.
Lemma lem3298842 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term463 _86426 q p x) = (term298 _86426 q p x).
Proof. exact (eq_refl (term463 _86426 q p x)). Qed.
Lemma lem3298843 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term470 _86426 q p) = (term461 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3298842 _86426 q p x)). Qed.
Lemma lem3298844 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298845 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term471 _86426 q p) = (term472 _86426 q p).
Proof. exact (MK_COMB (@lem3298844 _86426) (@lem3298843 _86426 q p)). Qed.
Lemma lem3298846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298847 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term473 _86426 q p) = (term474 _86426 q p).
Proof. exact (MK_COMB (@lem3298846) (@lem3298845 _86426 q p)). Qed.
Lemma lem3298848 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term465 _86426 q p x) = (term295 _86426 q p x).
Proof. exact (eq_refl (term465 _86426 q p x)). Qed.
Lemma lem3298849 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term475 _86426 q p) = (term462 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3298848 _86426 q p x)). Qed.
Lemma lem3298850 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3298851 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term476 _86426 q p) = (term477 _86426 q p).
Proof. exact (MK_COMB (@lem3298850 _86426) (@lem3298849 _86426 q p)). Qed.
Lemma lem3298852 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term460 _86426 q p) = (term478 _86426 q p).
Proof. exact (MK_COMB (@lem3298847 _86426 q p) (@lem3298851 _86426 q p)). Qed.
Lemma lem3298853 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : ((term459 _86426 q p) = (term460 _86426 q p)) = ((term312 _86426 q p) = (term478 _86426 q p)).
Proof. exact (MK_COMB (@lem3298841 _86426 q p) (@lem3298852 _86426 q p)). Qed.
Lemma lem3298854 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term312 _86426 q p) = (term478 _86426 q p).
Proof. exact (EQ_MP (@lem3298853 _86426 q p) (@lem3298831 _86426 q p)). Qed.
Lemma lem3298951 {_86426 : Type'} (q : _86426 -> Prop) : (term319 _86426 q) = (term479 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298854 _86426 q p)). Qed.
Lemma lem3298952 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298953 {_86426 : Type'} (q : _86426 -> Prop) : (term320 _86426 q) = (term480 _86426 q).
Proof. exact (MK_COMB (@lem3298952 _86426) (@lem3298951 _86426 q)). Qed.
Lemma lem3298955 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3298956 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3298955 (_86426 -> Prop) P Q). Qed.
Lemma lem3298957 {_86426 : Type'} (q : _86426 -> Prop) : (term483 _86426 q) = (term484 _86426 q).
Proof. exact (@lem3298956 _86426 (term485 _86426 q) (term486 _86426 q)). Qed.
Lemma lem3298958 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term487 _86426 q p) = (term472 _86426 q p).
Proof. exact (eq_refl (term487 _86426 q p)). Qed.
Lemma lem3298959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298960 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term488 _86426 q p) = (term474 _86426 q p).
Proof. exact (MK_COMB (@lem3298959) (@lem3298958 _86426 q p)). Qed.
Lemma lem3298961 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term489 _86426 q p) = (term477 _86426 q p).
Proof. exact (eq_refl (term489 _86426 q p)). Qed.
Lemma lem3298962 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term490 _86426 q p) = (term478 _86426 q p).
Proof. exact (MK_COMB (@lem3298960 _86426 q p) (@lem3298961 _86426 q p)). Qed.
Lemma lem3298963 {_86426 : Type'} (q : _86426 -> Prop) : (term491 _86426 q) = (term479 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298962 _86426 q p)). Qed.
Lemma lem3298964 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298965 {_86426 : Type'} (q : _86426 -> Prop) : (term483 _86426 q) = (term480 _86426 q).
Proof. exact (MK_COMB (@lem3298964 _86426) (@lem3298963 _86426 q)). Qed.
Lemma lem3298966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3298967 {_86426 : Type'} (q : _86426 -> Prop) : (term492 _86426 q) = (term493 _86426 q).
Proof. exact (MK_COMB (@lem3298966) (@lem3298965 _86426 q)). Qed.
Lemma lem3298968 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term487 _86426 q p) = (term472 _86426 q p).
Proof. exact (eq_refl (term487 _86426 q p)). Qed.
Lemma lem3298969 {_86426 : Type'} (q : _86426 -> Prop) : (term494 _86426 q) = (term485 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298968 _86426 q p)). Qed.
Lemma lem3298970 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298971 {_86426 : Type'} (q : _86426 -> Prop) : (term495 _86426 q) = (term496 _86426 q).
Proof. exact (MK_COMB (@lem3298970 _86426) (@lem3298969 _86426 q)). Qed.
Lemma lem3298972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3298973 {_86426 : Type'} (q : _86426 -> Prop) : (term497 _86426 q) = (term498 _86426 q).
Proof. exact (MK_COMB (@lem3298972) (@lem3298971 _86426 q)). Qed.
Lemma lem3298974 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term489 _86426 q p) = (term477 _86426 q p).
Proof. exact (eq_refl (term489 _86426 q p)). Qed.
Lemma lem3298975 {_86426 : Type'} (q : _86426 -> Prop) : (term499 _86426 q) = (term486 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3298974 _86426 q p)). Qed.
Lemma lem3298976 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3298977 {_86426 : Type'} (q : _86426 -> Prop) : (term500 _86426 q) = (term501 _86426 q).
Proof. exact (MK_COMB (@lem3298976 _86426) (@lem3298975 _86426 q)). Qed.
Lemma lem3298978 {_86426 : Type'} (q : _86426 -> Prop) : (term484 _86426 q) = (term502 _86426 q).
Proof. exact (MK_COMB (@lem3298973 _86426 q) (@lem3298977 _86426 q)). Qed.
Lemma lem3298979 {_86426 : Type'} (q : _86426 -> Prop) : ((term483 _86426 q) = (term484 _86426 q)) = ((term480 _86426 q) = (term502 _86426 q)).
Proof. exact (MK_COMB (@lem3298967 _86426 q) (@lem3298978 _86426 q)). Qed.
Lemma lem3298980 {_86426 : Type'} (q : _86426 -> Prop) : (term480 _86426 q) = (term502 _86426 q).
Proof. exact (EQ_MP (@lem3298979 _86426 q) (@lem3298957 _86426 q)). Qed.
Lemma lem3299085 {_86426 : Type'} (q : _86426 -> Prop) : (term320 _86426 q) = (term502 _86426 q).
Proof. exact (TRANS (@lem3298953 _86426 q) (@lem3298980 _86426 q)). Qed.
Lemma lem3299086 {_86426 : Type'} : (term325 _86426) = (term503 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299085 _86426 q)). Qed.
Lemma lem3299087 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299088 {_86426 : Type'} : (term326 _86426) = (term504 _86426).
Proof. exact (MK_COMB (@lem3299087 _86426) (@lem3299086 _86426)). Qed.
Lemma lem3299090 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299091 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3299090 (_86426 -> Prop) P Q). Qed.
Lemma lem3299092 {_86426 : Type'} : (term505 _86426) = (term506 _86426).
Proof. exact (@lem3299091 _86426 (term507 _86426) (term508 _86426)). Qed.
Lemma lem3299093 {_86426 : Type'} (q : _86426 -> Prop) : (term509 _86426 q) = (term496 _86426 q).
Proof. exact (eq_refl (term509 _86426 q)). Qed.
Lemma lem3299094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299095 {_86426 : Type'} (q : _86426 -> Prop) : (term510 _86426 q) = (term498 _86426 q).
Proof. exact (MK_COMB (@lem3299094) (@lem3299093 _86426 q)). Qed.
Lemma lem3299096 {_86426 : Type'} (q : _86426 -> Prop) : (term511 _86426 q) = (term501 _86426 q).
Proof. exact (eq_refl (term511 _86426 q)). Qed.
Lemma lem3299097 {_86426 : Type'} (q : _86426 -> Prop) : (term512 _86426 q) = (term502 _86426 q).
Proof. exact (MK_COMB (@lem3299095 _86426 q) (@lem3299096 _86426 q)). Qed.
Lemma lem3299098 {_86426 : Type'} : (term513 _86426) = (term503 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299097 _86426 q)). Qed.
Lemma lem3299099 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299100 {_86426 : Type'} : (term505 _86426) = (term504 _86426).
Proof. exact (MK_COMB (@lem3299099 _86426) (@lem3299098 _86426)). Qed.
Lemma lem3299101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299102 {_86426 : Type'} : (term514 _86426) = (term515 _86426).
Proof. exact (MK_COMB (@lem3299101) (@lem3299100 _86426)). Qed.
Lemma lem3299103 {_86426 : Type'} (q : _86426 -> Prop) : (term509 _86426 q) = (term496 _86426 q).
Proof. exact (eq_refl (term509 _86426 q)). Qed.
Lemma lem3299104 {_86426 : Type'} : (term516 _86426) = (term507 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299103 _86426 q)). Qed.
Lemma lem3299105 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299106 {_86426 : Type'} : (term517 _86426) = (term518 _86426).
Proof. exact (MK_COMB (@lem3299105 _86426) (@lem3299104 _86426)). Qed.
Lemma lem3299107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299108 {_86426 : Type'} : (term519 _86426) = (term520 _86426).
Proof. exact (MK_COMB (@lem3299107) (@lem3299106 _86426)). Qed.
Lemma lem3299109 {_86426 : Type'} (q : _86426 -> Prop) : (term511 _86426 q) = (term501 _86426 q).
Proof. exact (eq_refl (term511 _86426 q)). Qed.
Lemma lem3299110 {_86426 : Type'} : (term521 _86426) = (term508 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299109 _86426 q)). Qed.
Lemma lem3299111 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299112 {_86426 : Type'} : (term522 _86426) = (term523 _86426).
Proof. exact (MK_COMB (@lem3299111 _86426) (@lem3299110 _86426)). Qed.
Lemma lem3299113 {_86426 : Type'} : (term506 _86426) = (term524 _86426).
Proof. exact (MK_COMB (@lem3299108 _86426) (@lem3299112 _86426)). Qed.
Lemma lem3299114 {_86426 : Type'} : ((term505 _86426) = (term506 _86426)) = ((term504 _86426) = (term524 _86426)).
Proof. exact (MK_COMB (@lem3299102 _86426) (@lem3299113 _86426)). Qed.
Lemma lem3299115 {_86426 : Type'} : (term504 _86426) = (term524 _86426).
Proof. exact (EQ_MP (@lem3299114 _86426) (@lem3299092 _86426)). Qed.
Lemma lem3299228 {_86426 : Type'} : (term326 _86426) = (term524 _86426).
Proof. exact (TRANS (@lem3299088 _86426) (@lem3299115 _86426)). Qed.
Lemma lem3299229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299230 {_86426 : Type'} : (term454 _86426) = (term525 _86426).
Proof. exact (MK_COMB (@lem3299229) (@lem3299228 _86426)). Qed.
Lemma lem3299244 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299245 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term457 _86426 P Q) = (term458 _86426 P Q).
Proof. exact (@lem3299244 _86426 P Q). Qed.
Lemma lem3299246 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term526 _86426 p q r) = (term527 _86426 p q r).
Proof. exact (@lem3299245 _86426 (term528 _86426 p q r) (term529 _86426 p q r)). Qed.
Lemma lem3299247 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term530 _86426 p q r x) = (term341 _86426 p q r x).
Proof. exact (eq_refl (term530 _86426 p q r x)). Qed.
Lemma lem3299248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299249 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term531 _86426 p q r x) = (term343 _86426 p q r x).
Proof. exact (MK_COMB (@lem3299248) (@lem3299247 _86426 p q r x)). Qed.
Lemma lem3299250 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term532 _86426 p q r x) = (term338 _86426 p q r x).
Proof. exact (eq_refl (term532 _86426 p q r x)). Qed.
Lemma lem3299251 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term533 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (MK_COMB (@lem3299249 _86426 p q r x) (@lem3299250 _86426 p q r x)). Qed.
Lemma lem3299252 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term534 _86426 p q r) = (term352 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3299251 _86426 p q r x)). Qed.
Lemma lem3299253 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3299254 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term526 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (MK_COMB (@lem3299253 _86426) (@lem3299252 _86426 p q r)). Qed.
Lemma lem3299255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299256 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term535 _86426 p q r) = (term536 _86426 p q r).
Proof. exact (MK_COMB (@lem3299255) (@lem3299254 _86426 p q r)). Qed.
Lemma lem3299257 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term530 _86426 p q r x) = (term341 _86426 p q r x).
Proof. exact (eq_refl (term530 _86426 p q r x)). Qed.
Lemma lem3299258 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term537 _86426 p q r) = (term528 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3299257 _86426 p q r x)). Qed.
Lemma lem3299259 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3299260 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term538 _86426 p q r) = (term539 _86426 p q r).
Proof. exact (MK_COMB (@lem3299259 _86426) (@lem3299258 _86426 p q r)). Qed.
Lemma lem3299261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299262 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term540 _86426 p q r) = (term541 _86426 p q r).
Proof. exact (MK_COMB (@lem3299261) (@lem3299260 _86426 p q r)). Qed.
Lemma lem3299263 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term532 _86426 p q r x) = (term338 _86426 p q r x).
Proof. exact (eq_refl (term532 _86426 p q r x)). Qed.
Lemma lem3299264 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term542 _86426 p q r) = (term529 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3299263 _86426 p q r x)). Qed.
Lemma lem3299265 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3299266 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term543 _86426 p q r) = (term544 _86426 p q r).
Proof. exact (MK_COMB (@lem3299265 _86426) (@lem3299264 _86426 p q r)). Qed.
Lemma lem3299267 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term527 _86426 p q r) = (term545 _86426 p q r).
Proof. exact (MK_COMB (@lem3299262 _86426 p q r) (@lem3299266 _86426 p q r)). Qed.
Lemma lem3299268 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : ((term526 _86426 p q r) = (term527 _86426 p q r)) = ((term353 _86426 p q r) = (term545 _86426 p q r)).
Proof. exact (MK_COMB (@lem3299256 _86426 p q r) (@lem3299267 _86426 p q r)). Qed.
Lemma lem3299269 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term353 _86426 p q r) = (term545 _86426 p q r).
Proof. exact (EQ_MP (@lem3299268 _86426 p q r) (@lem3299246 _86426 p q r)). Qed.
Lemma lem3299366 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term358 _86426 p q) = (term546 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299269 _86426 p q r)). Qed.
Lemma lem3299367 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299368 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term359 _86426 p q) = (term547 _86426 p q).
Proof. exact (MK_COMB (@lem3299367 _86426) (@lem3299366 _86426 p q)). Qed.
Lemma lem3299370 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299371 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3299370 (_86426 -> Prop) P Q). Qed.
Lemma lem3299372 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term548 _86426 p q) = (term549 _86426 p q).
Proof. exact (@lem3299371 _86426 (term550 _86426 p q) (term551 _86426 p q)). Qed.
Lemma lem3299373 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term552 _86426 p q r) = (term539 _86426 p q r).
Proof. exact (eq_refl (term552 _86426 p q r)). Qed.
Lemma lem3299374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299375 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term553 _86426 p q r) = (term541 _86426 p q r).
Proof. exact (MK_COMB (@lem3299374) (@lem3299373 _86426 p q r)). Qed.
Lemma lem3299376 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term554 _86426 p q r) = (term544 _86426 p q r).
Proof. exact (eq_refl (term554 _86426 p q r)). Qed.
Lemma lem3299377 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term555 _86426 p q r) = (term545 _86426 p q r).
Proof. exact (MK_COMB (@lem3299375 _86426 p q r) (@lem3299376 _86426 p q r)). Qed.
Lemma lem3299378 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term556 _86426 p q) = (term546 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299377 _86426 p q r)). Qed.
Lemma lem3299379 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299380 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term548 _86426 p q) = (term547 _86426 p q).
Proof. exact (MK_COMB (@lem3299379 _86426) (@lem3299378 _86426 p q)). Qed.
Lemma lem3299381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299382 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term557 _86426 p q) = (term558 _86426 p q).
Proof. exact (MK_COMB (@lem3299381) (@lem3299380 _86426 p q)). Qed.
Lemma lem3299383 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term552 _86426 p q r) = (term539 _86426 p q r).
Proof. exact (eq_refl (term552 _86426 p q r)). Qed.
Lemma lem3299384 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term559 _86426 p q) = (term550 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299383 _86426 p q r)). Qed.
Lemma lem3299385 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299386 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term560 _86426 p q) = (term561 _86426 p q).
Proof. exact (MK_COMB (@lem3299385 _86426) (@lem3299384 _86426 p q)). Qed.
Lemma lem3299387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299388 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term562 _86426 p q) = (term563 _86426 p q).
Proof. exact (MK_COMB (@lem3299387) (@lem3299386 _86426 p q)). Qed.
Lemma lem3299389 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term554 _86426 p q r) = (term544 _86426 p q r).
Proof. exact (eq_refl (term554 _86426 p q r)). Qed.
Lemma lem3299390 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term564 _86426 p q) = (term551 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299389 _86426 p q r)). Qed.
Lemma lem3299391 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299392 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term565 _86426 p q) = (term566 _86426 p q).
Proof. exact (MK_COMB (@lem3299391 _86426) (@lem3299390 _86426 p q)). Qed.
Lemma lem3299393 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term549 _86426 p q) = (term567 _86426 p q).
Proof. exact (MK_COMB (@lem3299388 _86426 p q) (@lem3299392 _86426 p q)). Qed.
Lemma lem3299394 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term548 _86426 p q) = (term549 _86426 p q)) = ((term547 _86426 p q) = (term567 _86426 p q)).
Proof. exact (MK_COMB (@lem3299382 _86426 p q) (@lem3299393 _86426 p q)). Qed.
Lemma lem3299395 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term547 _86426 p q) = (term567 _86426 p q).
Proof. exact (EQ_MP (@lem3299394 _86426 p q) (@lem3299372 _86426 p q)). Qed.
Lemma lem3299500 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term359 _86426 p q) = (term567 _86426 p q).
Proof. exact (TRANS (@lem3299368 _86426 p q) (@lem3299395 _86426 p q)). Qed.
Lemma lem3299501 {_86426 : Type'} (q : _86426 -> Prop) : (term364 _86426 q) = (term568 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3299500 _86426 p q)). Qed.
Lemma lem3299502 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299503 {_86426 : Type'} (q : _86426 -> Prop) : (term365 _86426 q) = (term569 _86426 q).
Proof. exact (MK_COMB (@lem3299502 _86426) (@lem3299501 _86426 q)). Qed.
Lemma lem3299505 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299506 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3299505 (_86426 -> Prop) P Q). Qed.
Lemma lem3299507 {_86426 : Type'} (q : _86426 -> Prop) : (term570 _86426 q) = (term571 _86426 q).
Proof. exact (@lem3299506 _86426 (term572 _86426 q) (term573 _86426 q)). Qed.
Lemma lem3299508 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term574 _86426 q p) = (term561 _86426 p q).
Proof. exact (eq_refl (term574 _86426 q p)). Qed.
Lemma lem3299509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299510 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term575 _86426 q p) = (term563 _86426 p q).
Proof. exact (MK_COMB (@lem3299509) (@lem3299508 _86426 p q)). Qed.
Lemma lem3299511 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term576 _86426 q p) = (term566 _86426 p q).
Proof. exact (eq_refl (term576 _86426 q p)). Qed.
Lemma lem3299512 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term577 _86426 q p) = (term567 _86426 p q).
Proof. exact (MK_COMB (@lem3299510 _86426 p q) (@lem3299511 _86426 p q)). Qed.
Lemma lem3299513 {_86426 : Type'} (q : _86426 -> Prop) : (term578 _86426 q) = (term568 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3299512 _86426 p q)). Qed.
Lemma lem3299514 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299515 {_86426 : Type'} (q : _86426 -> Prop) : (term570 _86426 q) = (term569 _86426 q).
Proof. exact (MK_COMB (@lem3299514 _86426) (@lem3299513 _86426 q)). Qed.
Lemma lem3299516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299517 {_86426 : Type'} (q : _86426 -> Prop) : (term579 _86426 q) = (term580 _86426 q).
Proof. exact (MK_COMB (@lem3299516) (@lem3299515 _86426 q)). Qed.
Lemma lem3299518 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term574 _86426 q p) = (term561 _86426 p q).
Proof. exact (eq_refl (term574 _86426 q p)). Qed.
Lemma lem3299519 {_86426 : Type'} (q : _86426 -> Prop) : (term581 _86426 q) = (term572 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3299518 _86426 p q)). Qed.
Lemma lem3299520 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299521 {_86426 : Type'} (q : _86426 -> Prop) : (term582 _86426 q) = (term583 _86426 q).
Proof. exact (MK_COMB (@lem3299520 _86426) (@lem3299519 _86426 q)). Qed.
Lemma lem3299522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299523 {_86426 : Type'} (q : _86426 -> Prop) : (term584 _86426 q) = (term585 _86426 q).
Proof. exact (MK_COMB (@lem3299522) (@lem3299521 _86426 q)). Qed.
Lemma lem3299524 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term576 _86426 q p) = (term566 _86426 p q).
Proof. exact (eq_refl (term576 _86426 q p)). Qed.
Lemma lem3299525 {_86426 : Type'} (q : _86426 -> Prop) : (term586 _86426 q) = (term573 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3299524 _86426 p q)). Qed.
Lemma lem3299526 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299527 {_86426 : Type'} (q : _86426 -> Prop) : (term587 _86426 q) = (term588 _86426 q).
Proof. exact (MK_COMB (@lem3299526 _86426) (@lem3299525 _86426 q)). Qed.
Lemma lem3299528 {_86426 : Type'} (q : _86426 -> Prop) : (term571 _86426 q) = (term589 _86426 q).
Proof. exact (MK_COMB (@lem3299523 _86426 q) (@lem3299527 _86426 q)). Qed.
Lemma lem3299529 {_86426 : Type'} (q : _86426 -> Prop) : ((term570 _86426 q) = (term571 _86426 q)) = ((term569 _86426 q) = (term589 _86426 q)).
Proof. exact (MK_COMB (@lem3299517 _86426 q) (@lem3299528 _86426 q)). Qed.
Lemma lem3299530 {_86426 : Type'} (q : _86426 -> Prop) : (term569 _86426 q) = (term589 _86426 q).
Proof. exact (EQ_MP (@lem3299529 _86426 q) (@lem3299507 _86426 q)). Qed.
Lemma lem3299643 {_86426 : Type'} (q : _86426 -> Prop) : (term365 _86426 q) = (term589 _86426 q).
Proof. exact (TRANS (@lem3299503 _86426 q) (@lem3299530 _86426 q)). Qed.
Lemma lem3299644 {_86426 : Type'} : (term370 _86426) = (term590 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299643 _86426 q)). Qed.
Lemma lem3299645 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299646 {_86426 : Type'} : (term371 _86426) = (term591 _86426).
Proof. exact (MK_COMB (@lem3299645 _86426) (@lem3299644 _86426)). Qed.
Lemma lem3299648 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299649 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3299648 (_86426 -> Prop) P Q). Qed.
Lemma lem3299650 {_86426 : Type'} : (term592 _86426) = (term593 _86426).
Proof. exact (@lem3299649 _86426 (term594 _86426) (term595 _86426)). Qed.
Lemma lem3299651 {_86426 : Type'} (q : _86426 -> Prop) : (term596 _86426 q) = (term583 _86426 q).
Proof. exact (eq_refl (term596 _86426 q)). Qed.
Lemma lem3299652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299653 {_86426 : Type'} (q : _86426 -> Prop) : (term597 _86426 q) = (term585 _86426 q).
Proof. exact (MK_COMB (@lem3299652) (@lem3299651 _86426 q)). Qed.
Lemma lem3299654 {_86426 : Type'} (q : _86426 -> Prop) : (term598 _86426 q) = (term588 _86426 q).
Proof. exact (eq_refl (term598 _86426 q)). Qed.
Lemma lem3299655 {_86426 : Type'} (q : _86426 -> Prop) : (term599 _86426 q) = (term589 _86426 q).
Proof. exact (MK_COMB (@lem3299653 _86426 q) (@lem3299654 _86426 q)). Qed.
Lemma lem3299656 {_86426 : Type'} : (term600 _86426) = (term590 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299655 _86426 q)). Qed.
Lemma lem3299657 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299658 {_86426 : Type'} : (term592 _86426) = (term591 _86426).
Proof. exact (MK_COMB (@lem3299657 _86426) (@lem3299656 _86426)). Qed.
Lemma lem3299659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299660 {_86426 : Type'} : (term601 _86426) = (term602 _86426).
Proof. exact (MK_COMB (@lem3299659) (@lem3299658 _86426)). Qed.
Lemma lem3299661 {_86426 : Type'} (q : _86426 -> Prop) : (term596 _86426 q) = (term583 _86426 q).
Proof. exact (eq_refl (term596 _86426 q)). Qed.
Lemma lem3299662 {_86426 : Type'} : (term603 _86426) = (term594 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299661 _86426 q)). Qed.
Lemma lem3299663 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299664 {_86426 : Type'} : (term604 _86426) = (term605 _86426).
Proof. exact (MK_COMB (@lem3299663 _86426) (@lem3299662 _86426)). Qed.
Lemma lem3299665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299666 {_86426 : Type'} : (term606 _86426) = (term607 _86426).
Proof. exact (MK_COMB (@lem3299665) (@lem3299664 _86426)). Qed.
Lemma lem3299667 {_86426 : Type'} (q : _86426 -> Prop) : (term598 _86426 q) = (term588 _86426 q).
Proof. exact (eq_refl (term598 _86426 q)). Qed.
Lemma lem3299668 {_86426 : Type'} : (term608 _86426) = (term595 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3299667 _86426 q)). Qed.
Lemma lem3299669 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299670 {_86426 : Type'} : (term609 _86426) = (term610 _86426).
Proof. exact (MK_COMB (@lem3299669 _86426) (@lem3299668 _86426)). Qed.
Lemma lem3299671 {_86426 : Type'} : (term593 _86426) = (term611 _86426).
Proof. exact (MK_COMB (@lem3299666 _86426) (@lem3299670 _86426)). Qed.
Lemma lem3299672 {_86426 : Type'} : ((term592 _86426) = (term593 _86426)) = ((term591 _86426) = (term611 _86426)).
Proof. exact (MK_COMB (@lem3299660 _86426) (@lem3299671 _86426)). Qed.
Lemma lem3299673 {_86426 : Type'} : (term591 _86426) = (term611 _86426).
Proof. exact (EQ_MP (@lem3299672 _86426) (@lem3299650 _86426)). Qed.
Lemma lem3299794 {_86426 : Type'} : (term371 _86426) = (term611 _86426).
Proof. exact (TRANS (@lem3299646 _86426) (@lem3299673 _86426)). Qed.
Lemma lem3299795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299796 {_86426 : Type'} : (term449 _86426) = (term612 _86426).
Proof. exact (MK_COMB (@lem3299795) (@lem3299794 _86426)). Qed.
Lemma lem3299810 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299811 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term457 _86426 P Q) = (term458 _86426 P Q).
Proof. exact (@lem3299810 _86426 P Q). Qed.
Lemma lem3299812 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term613 _86426 q p r) = (term614 _86426 q p r).
Proof. exact (@lem3299811 _86426 (term615 _86426 q p r) (term616 _86426 q p r)). Qed.
Lemma lem3299813 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term617 _86426 q p r x) = (term378 _86426 q p r x).
Proof. exact (eq_refl (term617 _86426 q p r x)). Qed.
Lemma lem3299814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299815 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term618 _86426 q p r x) = (term380 _86426 q p r x).
Proof. exact (MK_COMB (@lem3299814) (@lem3299813 _86426 q p r x)). Qed.
Lemma lem3299816 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term619 _86426 q p r x) = (term375 _86426 q p r x).
Proof. exact (eq_refl (term619 _86426 q p r x)). Qed.
Lemma lem3299817 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term620 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (MK_COMB (@lem3299815 _86426 q p r x) (@lem3299816 _86426 q p r x)). Qed.
Lemma lem3299818 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term621 _86426 q p r) = (term389 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3299817 _86426 q p r x)). Qed.
Lemma lem3299819 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3299820 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term613 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (MK_COMB (@lem3299819 _86426) (@lem3299818 _86426 q p r)). Qed.
Lemma lem3299821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299822 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term622 _86426 q p r) = (term623 _86426 q p r).
Proof. exact (MK_COMB (@lem3299821) (@lem3299820 _86426 q p r)). Qed.
Lemma lem3299823 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term617 _86426 q p r x) = (term378 _86426 q p r x).
Proof. exact (eq_refl (term617 _86426 q p r x)). Qed.
Lemma lem3299824 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term624 _86426 q p r) = (term615 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3299823 _86426 q p r x)). Qed.
Lemma lem3299825 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3299826 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term625 _86426 q p r) = (term626 _86426 q p r).
Proof. exact (MK_COMB (@lem3299825 _86426) (@lem3299824 _86426 q p r)). Qed.
Lemma lem3299827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299828 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term627 _86426 q p r) = (term628 _86426 q p r).
Proof. exact (MK_COMB (@lem3299827) (@lem3299826 _86426 q p r)). Qed.
Lemma lem3299829 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term619 _86426 q p r x) = (term375 _86426 q p r x).
Proof. exact (eq_refl (term619 _86426 q p r x)). Qed.
Lemma lem3299830 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term629 _86426 q p r) = (term616 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3299829 _86426 q p r x)). Qed.
Lemma lem3299831 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3299832 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term630 _86426 q p r) = (term631 _86426 q p r).
Proof. exact (MK_COMB (@lem3299831 _86426) (@lem3299830 _86426 q p r)). Qed.
Lemma lem3299833 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term614 _86426 q p r) = (term632 _86426 q p r).
Proof. exact (MK_COMB (@lem3299828 _86426 q p r) (@lem3299832 _86426 q p r)). Qed.
Lemma lem3299834 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : ((term613 _86426 q p r) = (term614 _86426 q p r)) = ((term390 _86426 q p r) = (term632 _86426 q p r)).
Proof. exact (MK_COMB (@lem3299822 _86426 q p r) (@lem3299833 _86426 q p r)). Qed.
Lemma lem3299835 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term390 _86426 q p r) = (term632 _86426 q p r).
Proof. exact (EQ_MP (@lem3299834 _86426 q p r) (@lem3299812 _86426 q p r)). Qed.
Lemma lem3299932 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term395 _86426 q p) = (term633 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299835 _86426 q p r)). Qed.
Lemma lem3299933 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299934 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term396 _86426 q p) = (term634 _86426 q p).
Proof. exact (MK_COMB (@lem3299933 _86426) (@lem3299932 _86426 q p)). Qed.
Lemma lem3299936 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3299937 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3299936 (_86426 -> Prop) P Q). Qed.
Lemma lem3299938 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term635 _86426 q p) = (term636 _86426 q p).
Proof. exact (@lem3299937 _86426 (term637 _86426 q p) (term638 _86426 q p)). Qed.
Lemma lem3299939 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term639 _86426 q p r) = (term626 _86426 q p r).
Proof. exact (eq_refl (term639 _86426 q p r)). Qed.
Lemma lem3299940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299941 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term640 _86426 q p r) = (term628 _86426 q p r).
Proof. exact (MK_COMB (@lem3299940) (@lem3299939 _86426 q p r)). Qed.
Lemma lem3299942 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term641 _86426 q p r) = (term631 _86426 q p r).
Proof. exact (eq_refl (term641 _86426 q p r)). Qed.
Lemma lem3299943 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term642 _86426 q p r) = (term632 _86426 q p r).
Proof. exact (MK_COMB (@lem3299941 _86426 q p r) (@lem3299942 _86426 q p r)). Qed.
Lemma lem3299944 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term643 _86426 q p) = (term633 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299943 _86426 q p r)). Qed.
Lemma lem3299945 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299946 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term635 _86426 q p) = (term634 _86426 q p).
Proof. exact (MK_COMB (@lem3299945 _86426) (@lem3299944 _86426 q p)). Qed.
Lemma lem3299947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3299948 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term644 _86426 q p) = (term645 _86426 q p).
Proof. exact (MK_COMB (@lem3299947) (@lem3299946 _86426 q p)). Qed.
Lemma lem3299949 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term639 _86426 q p r) = (term626 _86426 q p r).
Proof. exact (eq_refl (term639 _86426 q p r)). Qed.
Lemma lem3299950 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term646 _86426 q p) = (term637 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299949 _86426 q p r)). Qed.
Lemma lem3299951 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299952 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term647 _86426 q p) = (term648 _86426 q p).
Proof. exact (MK_COMB (@lem3299951 _86426) (@lem3299950 _86426 q p)). Qed.
Lemma lem3299953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3299954 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term649 _86426 q p) = (term650 _86426 q p).
Proof. exact (MK_COMB (@lem3299953) (@lem3299952 _86426 q p)). Qed.
Lemma lem3299955 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term641 _86426 q p r) = (term631 _86426 q p r).
Proof. exact (eq_refl (term641 _86426 q p r)). Qed.
Lemma lem3299956 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term651 _86426 q p) = (term638 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3299955 _86426 q p r)). Qed.
Lemma lem3299957 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3299958 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term652 _86426 q p) = (term653 _86426 q p).
Proof. exact (MK_COMB (@lem3299957 _86426) (@lem3299956 _86426 q p)). Qed.
Lemma lem3299959 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term636 _86426 q p) = (term654 _86426 q p).
Proof. exact (MK_COMB (@lem3299954 _86426 q p) (@lem3299958 _86426 q p)). Qed.
Lemma lem3299960 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : ((term635 _86426 q p) = (term636 _86426 q p)) = ((term634 _86426 q p) = (term654 _86426 q p)).
Proof. exact (MK_COMB (@lem3299948 _86426 q p) (@lem3299959 _86426 q p)). Qed.
Lemma lem3299961 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term634 _86426 q p) = (term654 _86426 q p).
Proof. exact (EQ_MP (@lem3299960 _86426 q p) (@lem3299938 _86426 q p)). Qed.
Lemma lem3300066 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term396 _86426 q p) = (term654 _86426 q p).
Proof. exact (TRANS (@lem3299934 _86426 q p) (@lem3299961 _86426 q p)). Qed.
Lemma lem3300067 {_86426 : Type'} (q : _86426 -> Prop) : (term401 _86426 q) = (term655 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300066 _86426 q p)). Qed.
Lemma lem3300068 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300069 {_86426 : Type'} (q : _86426 -> Prop) : (term402 _86426 q) = (term656 _86426 q).
Proof. exact (MK_COMB (@lem3300068 _86426) (@lem3300067 _86426 q)). Qed.
Lemma lem3300071 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3300072 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3300071 (_86426 -> Prop) P Q). Qed.
Lemma lem3300073 {_86426 : Type'} (q : _86426 -> Prop) : (term657 _86426 q) = (term658 _86426 q).
Proof. exact (@lem3300072 _86426 (term659 _86426 q) (term660 _86426 q)). Qed.
Lemma lem3300074 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term661 _86426 q p) = (term648 _86426 q p).
Proof. exact (eq_refl (term661 _86426 q p)). Qed.
Lemma lem3300075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300076 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term662 _86426 q p) = (term650 _86426 q p).
Proof. exact (MK_COMB (@lem3300075) (@lem3300074 _86426 q p)). Qed.
Lemma lem3300077 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term663 _86426 q p) = (term653 _86426 q p).
Proof. exact (eq_refl (term663 _86426 q p)). Qed.
Lemma lem3300078 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term664 _86426 q p) = (term654 _86426 q p).
Proof. exact (MK_COMB (@lem3300076 _86426 q p) (@lem3300077 _86426 q p)). Qed.
Lemma lem3300079 {_86426 : Type'} (q : _86426 -> Prop) : (term665 _86426 q) = (term655 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300078 _86426 q p)). Qed.
Lemma lem3300080 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300081 {_86426 : Type'} (q : _86426 -> Prop) : (term657 _86426 q) = (term656 _86426 q).
Proof. exact (MK_COMB (@lem3300080 _86426) (@lem3300079 _86426 q)). Qed.
Lemma lem3300082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300083 {_86426 : Type'} (q : _86426 -> Prop) : (term666 _86426 q) = (term667 _86426 q).
Proof. exact (MK_COMB (@lem3300082) (@lem3300081 _86426 q)). Qed.
Lemma lem3300084 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term661 _86426 q p) = (term648 _86426 q p).
Proof. exact (eq_refl (term661 _86426 q p)). Qed.
Lemma lem3300085 {_86426 : Type'} (q : _86426 -> Prop) : (term668 _86426 q) = (term659 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300084 _86426 q p)). Qed.
Lemma lem3300086 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300087 {_86426 : Type'} (q : _86426 -> Prop) : (term669 _86426 q) = (term670 _86426 q).
Proof. exact (MK_COMB (@lem3300086 _86426) (@lem3300085 _86426 q)). Qed.
Lemma lem3300088 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300089 {_86426 : Type'} (q : _86426 -> Prop) : (term671 _86426 q) = (term672 _86426 q).
Proof. exact (MK_COMB (@lem3300088) (@lem3300087 _86426 q)). Qed.
Lemma lem3300090 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term663 _86426 q p) = (term653 _86426 q p).
Proof. exact (eq_refl (term663 _86426 q p)). Qed.
Lemma lem3300091 {_86426 : Type'} (q : _86426 -> Prop) : (term673 _86426 q) = (term660 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300090 _86426 q p)). Qed.
Lemma lem3300092 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300093 {_86426 : Type'} (q : _86426 -> Prop) : (term674 _86426 q) = (term675 _86426 q).
Proof. exact (MK_COMB (@lem3300092 _86426) (@lem3300091 _86426 q)). Qed.
Lemma lem3300094 {_86426 : Type'} (q : _86426 -> Prop) : (term658 _86426 q) = (term676 _86426 q).
Proof. exact (MK_COMB (@lem3300089 _86426 q) (@lem3300093 _86426 q)). Qed.
Lemma lem3300095 {_86426 : Type'} (q : _86426 -> Prop) : ((term657 _86426 q) = (term658 _86426 q)) = ((term656 _86426 q) = (term676 _86426 q)).
Proof. exact (MK_COMB (@lem3300083 _86426 q) (@lem3300094 _86426 q)). Qed.
Lemma lem3300096 {_86426 : Type'} (q : _86426 -> Prop) : (term656 _86426 q) = (term676 _86426 q).
Proof. exact (EQ_MP (@lem3300095 _86426 q) (@lem3300073 _86426 q)). Qed.
Lemma lem3300209 {_86426 : Type'} (q : _86426 -> Prop) : (term402 _86426 q) = (term676 _86426 q).
Proof. exact (TRANS (@lem3300069 _86426 q) (@lem3300096 _86426 q)). Qed.
Lemma lem3300210 {_86426 : Type'} : (term407 _86426) = (term677 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300209 _86426 q)). Qed.
Lemma lem3300211 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300212 {_86426 : Type'} : (term408 _86426) = (term678 _86426).
Proof. exact (MK_COMB (@lem3300211 _86426) (@lem3300210 _86426)). Qed.
Lemma lem3300214 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3300215 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3300214 (_86426 -> Prop) P Q). Qed.
Lemma lem3300216 {_86426 : Type'} : (term679 _86426) = (term680 _86426).
Proof. exact (@lem3300215 _86426 (term681 _86426) (term682 _86426)). Qed.
Lemma lem3300217 {_86426 : Type'} (q : _86426 -> Prop) : (term683 _86426 q) = (term670 _86426 q).
Proof. exact (eq_refl (term683 _86426 q)). Qed.
Lemma lem3300218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300219 {_86426 : Type'} (q : _86426 -> Prop) : (term684 _86426 q) = (term672 _86426 q).
Proof. exact (MK_COMB (@lem3300218) (@lem3300217 _86426 q)). Qed.
Lemma lem3300220 {_86426 : Type'} (q : _86426 -> Prop) : (term685 _86426 q) = (term675 _86426 q).
Proof. exact (eq_refl (term685 _86426 q)). Qed.
Lemma lem3300221 {_86426 : Type'} (q : _86426 -> Prop) : (term686 _86426 q) = (term676 _86426 q).
Proof. exact (MK_COMB (@lem3300219 _86426 q) (@lem3300220 _86426 q)). Qed.
Lemma lem3300222 {_86426 : Type'} : (term687 _86426) = (term677 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300221 _86426 q)). Qed.
Lemma lem3300223 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300224 {_86426 : Type'} : (term679 _86426) = (term678 _86426).
Proof. exact (MK_COMB (@lem3300223 _86426) (@lem3300222 _86426)). Qed.
Lemma lem3300225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300226 {_86426 : Type'} : (term688 _86426) = (term689 _86426).
Proof. exact (MK_COMB (@lem3300225) (@lem3300224 _86426)). Qed.
Lemma lem3300227 {_86426 : Type'} (q : _86426 -> Prop) : (term683 _86426 q) = (term670 _86426 q).
Proof. exact (eq_refl (term683 _86426 q)). Qed.
Lemma lem3300228 {_86426 : Type'} : (term690 _86426) = (term681 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300227 _86426 q)). Qed.
Lemma lem3300229 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300230 {_86426 : Type'} : (term691 _86426) = (term692 _86426).
Proof. exact (MK_COMB (@lem3300229 _86426) (@lem3300228 _86426)). Qed.
Lemma lem3300231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300232 {_86426 : Type'} : (term693 _86426) = (term694 _86426).
Proof. exact (MK_COMB (@lem3300231) (@lem3300230 _86426)). Qed.
Lemma lem3300233 {_86426 : Type'} (q : _86426 -> Prop) : (term685 _86426 q) = (term675 _86426 q).
Proof. exact (eq_refl (term685 _86426 q)). Qed.
Lemma lem3300234 {_86426 : Type'} : (term695 _86426) = (term682 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300233 _86426 q)). Qed.
Lemma lem3300235 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300236 {_86426 : Type'} : (term696 _86426) = (term697 _86426).
Proof. exact (MK_COMB (@lem3300235 _86426) (@lem3300234 _86426)). Qed.
Lemma lem3300237 {_86426 : Type'} : (term680 _86426) = (term698 _86426).
Proof. exact (MK_COMB (@lem3300232 _86426) (@lem3300236 _86426)). Qed.
Lemma lem3300238 {_86426 : Type'} : ((term679 _86426) = (term680 _86426)) = ((term678 _86426) = (term698 _86426)).
Proof. exact (MK_COMB (@lem3300226 _86426) (@lem3300237 _86426)). Qed.
Lemma lem3300239 {_86426 : Type'} : (term678 _86426) = (term698 _86426).
Proof. exact (EQ_MP (@lem3300238 _86426) (@lem3300216 _86426)). Qed.
Lemma lem3300360 {_86426 : Type'} : (term408 _86426) = (term698 _86426).
Proof. exact (TRANS (@lem3300212 _86426) (@lem3300239 _86426)). Qed.
Lemma lem3300361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300362 {_86426 : Type'} : (term444 _86426) = (term699 _86426).
Proof. exact (MK_COMB (@lem3300361) (@lem3300360 _86426)). Qed.
Lemma lem3300372 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3300373 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term457 _86426 P Q) = (term458 _86426 P Q).
Proof. exact (@lem3300372 _86426 P Q). Qed.
Lemma lem3300374 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term700 _86426 p q) = (term701 _86426 p q).
Proof. exact (@lem3300373 _86426 (term702 _86426 p q) (term703 _86426 p q)). Qed.
Lemma lem3300375 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term704 _86426 p q x) = (term418 _86426 p q x).
Proof. exact (eq_refl (term704 _86426 p q x)). Qed.
Lemma lem3300376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300377 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term705 _86426 p q x) = (term420 _86426 p q x).
Proof. exact (MK_COMB (@lem3300376) (@lem3300375 _86426 p q x)). Qed.
Lemma lem3300378 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term706 _86426 p q x) = (term415 _86426 p q x).
Proof. exact (eq_refl (term706 _86426 p q x)). Qed.
Lemma lem3300379 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term707 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (MK_COMB (@lem3300377 _86426 p q x) (@lem3300378 _86426 p q x)). Qed.
Lemma lem3300380 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term708 _86426 p q) = (term429 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3300379 _86426 p q x)). Qed.
Lemma lem3300381 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300382 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term700 _86426 p q) = (term430 _86426 p q).
Proof. exact (MK_COMB (@lem3300381 _86426) (@lem3300380 _86426 p q)). Qed.
Lemma lem3300383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300384 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term709 _86426 p q) = (term710 _86426 p q).
Proof. exact (MK_COMB (@lem3300383) (@lem3300382 _86426 p q)). Qed.
Lemma lem3300385 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term704 _86426 p q x) = (term418 _86426 p q x).
Proof. exact (eq_refl (term704 _86426 p q x)). Qed.
Lemma lem3300386 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term711 _86426 p q) = (term702 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3300385 _86426 p q x)). Qed.
Lemma lem3300387 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300388 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term712 _86426 p q) = (term713 _86426 p q).
Proof. exact (MK_COMB (@lem3300387 _86426) (@lem3300386 _86426 p q)). Qed.
Lemma lem3300389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300390 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term714 _86426 p q) = (term715 _86426 p q).
Proof. exact (MK_COMB (@lem3300389) (@lem3300388 _86426 p q)). Qed.
Lemma lem3300391 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term706 _86426 p q x) = (term415 _86426 p q x).
Proof. exact (eq_refl (term706 _86426 p q x)). Qed.
Lemma lem3300392 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term716 _86426 p q) = (term703 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3300391 _86426 p q x)). Qed.
Lemma lem3300393 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300394 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term717 _86426 p q) = (term718 _86426 p q).
Proof. exact (MK_COMB (@lem3300393 _86426) (@lem3300392 _86426 p q)). Qed.
Lemma lem3300395 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term701 _86426 p q) = (term719 _86426 p q).
Proof. exact (MK_COMB (@lem3300390 _86426 p q) (@lem3300394 _86426 p q)). Qed.
Lemma lem3300396 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term700 _86426 p q) = (term701 _86426 p q)) = ((term430 _86426 p q) = (term719 _86426 p q)).
Proof. exact (MK_COMB (@lem3300384 _86426 p q) (@lem3300395 _86426 p q)). Qed.
Lemma lem3300397 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term430 _86426 p q) = (term719 _86426 p q).
Proof. exact (EQ_MP (@lem3300396 _86426 p q) (@lem3300374 _86426 p q)). Qed.
Lemma lem3300494 {_86426 : Type'} (q : _86426 -> Prop) : (term435 _86426 q) = (term720 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300397 _86426 p q)). Qed.
Lemma lem3300495 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300496 {_86426 : Type'} (q : _86426 -> Prop) : (term436 _86426 q) = (term721 _86426 q).
Proof. exact (MK_COMB (@lem3300495 _86426) (@lem3300494 _86426 q)). Qed.
Lemma lem3300498 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3300499 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3300498 (_86426 -> Prop) P Q). Qed.
Lemma lem3300500 {_86426 : Type'} (q : _86426 -> Prop) : (term722 _86426 q) = (term723 _86426 q).
Proof. exact (@lem3300499 _86426 (term724 _86426 q) (term725 _86426 q)). Qed.
Lemma lem3300501 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term726 _86426 q p) = (term713 _86426 p q).
Proof. exact (eq_refl (term726 _86426 q p)). Qed.
Lemma lem3300502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300503 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term727 _86426 q p) = (term715 _86426 p q).
Proof. exact (MK_COMB (@lem3300502) (@lem3300501 _86426 p q)). Qed.
Lemma lem3300504 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term728 _86426 q p) = (term718 _86426 p q).
Proof. exact (eq_refl (term728 _86426 q p)). Qed.
Lemma lem3300505 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term729 _86426 q p) = (term719 _86426 p q).
Proof. exact (MK_COMB (@lem3300503 _86426 p q) (@lem3300504 _86426 p q)). Qed.
Lemma lem3300506 {_86426 : Type'} (q : _86426 -> Prop) : (term730 _86426 q) = (term720 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300505 _86426 p q)). Qed.
Lemma lem3300507 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300508 {_86426 : Type'} (q : _86426 -> Prop) : (term722 _86426 q) = (term721 _86426 q).
Proof. exact (MK_COMB (@lem3300507 _86426) (@lem3300506 _86426 q)). Qed.
Lemma lem3300509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300510 {_86426 : Type'} (q : _86426 -> Prop) : (term731 _86426 q) = (term732 _86426 q).
Proof. exact (MK_COMB (@lem3300509) (@lem3300508 _86426 q)). Qed.
Lemma lem3300511 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term726 _86426 q p) = (term713 _86426 p q).
Proof. exact (eq_refl (term726 _86426 q p)). Qed.
Lemma lem3300512 {_86426 : Type'} (q : _86426 -> Prop) : (term733 _86426 q) = (term724 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300511 _86426 p q)). Qed.
Lemma lem3300513 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300514 {_86426 : Type'} (q : _86426 -> Prop) : (term734 _86426 q) = (term735 _86426 q).
Proof. exact (MK_COMB (@lem3300513 _86426) (@lem3300512 _86426 q)). Qed.
Lemma lem3300515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300516 {_86426 : Type'} (q : _86426 -> Prop) : (term736 _86426 q) = (term737 _86426 q).
Proof. exact (MK_COMB (@lem3300515) (@lem3300514 _86426 q)). Qed.
Lemma lem3300517 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term728 _86426 q p) = (term718 _86426 p q).
Proof. exact (eq_refl (term728 _86426 q p)). Qed.
Lemma lem3300518 {_86426 : Type'} (q : _86426 -> Prop) : (term738 _86426 q) = (term725 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300517 _86426 p q)). Qed.
Lemma lem3300519 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300520 {_86426 : Type'} (q : _86426 -> Prop) : (term739 _86426 q) = (term740 _86426 q).
Proof. exact (MK_COMB (@lem3300519 _86426) (@lem3300518 _86426 q)). Qed.
Lemma lem3300521 {_86426 : Type'} (q : _86426 -> Prop) : (term723 _86426 q) = (term741 _86426 q).
Proof. exact (MK_COMB (@lem3300516 _86426 q) (@lem3300520 _86426 q)). Qed.
Lemma lem3300522 {_86426 : Type'} (q : _86426 -> Prop) : ((term722 _86426 q) = (term723 _86426 q)) = ((term721 _86426 q) = (term741 _86426 q)).
Proof. exact (MK_COMB (@lem3300510 _86426 q) (@lem3300521 _86426 q)). Qed.
Lemma lem3300523 {_86426 : Type'} (q : _86426 -> Prop) : (term721 _86426 q) = (term741 _86426 q).
Proof. exact (EQ_MP (@lem3300522 _86426 q) (@lem3300500 _86426 q)). Qed.
Lemma lem3300628 {_86426 : Type'} (q : _86426 -> Prop) : (term436 _86426 q) = (term741 _86426 q).
Proof. exact (TRANS (@lem3300496 _86426 q) (@lem3300523 _86426 q)). Qed.
Lemma lem3300629 {_86426 : Type'} : (term441 _86426) = (term742 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300628 _86426 q)). Qed.
Lemma lem3300630 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300631 {_86426 : Type'} : (term442 _86426) = (term743 _86426).
Proof. exact (MK_COMB (@lem3300630 _86426) (@lem3300629 _86426)). Qed.
Lemma lem3300633 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3300634 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term481 _86426 P Q) = (term482 _86426 P Q).
Proof. exact (@lem3300633 (_86426 -> Prop) P Q). Qed.
Lemma lem3300635 {_86426 : Type'} : (term744 _86426) = (term745 _86426).
Proof. exact (@lem3300634 _86426 (term746 _86426) (term747 _86426)). Qed.
Lemma lem3300636 {_86426 : Type'} (q : _86426 -> Prop) : (term748 _86426 q) = (term735 _86426 q).
Proof. exact (eq_refl (term748 _86426 q)). Qed.
Lemma lem3300637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300638 {_86426 : Type'} (q : _86426 -> Prop) : (term749 _86426 q) = (term737 _86426 q).
Proof. exact (MK_COMB (@lem3300637) (@lem3300636 _86426 q)). Qed.
Lemma lem3300639 {_86426 : Type'} (q : _86426 -> Prop) : (term750 _86426 q) = (term740 _86426 q).
Proof. exact (eq_refl (term750 _86426 q)). Qed.
Lemma lem3300640 {_86426 : Type'} (q : _86426 -> Prop) : (term751 _86426 q) = (term741 _86426 q).
Proof. exact (MK_COMB (@lem3300638 _86426 q) (@lem3300639 _86426 q)). Qed.
Lemma lem3300641 {_86426 : Type'} : (term752 _86426) = (term742 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300640 _86426 q)). Qed.
Lemma lem3300642 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300643 {_86426 : Type'} : (term744 _86426) = (term743 _86426).
Proof. exact (MK_COMB (@lem3300642 _86426) (@lem3300641 _86426)). Qed.
Lemma lem3300644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300645 {_86426 : Type'} : (term753 _86426) = (term754 _86426).
Proof. exact (MK_COMB (@lem3300644) (@lem3300643 _86426)). Qed.
Lemma lem3300646 {_86426 : Type'} (q : _86426 -> Prop) : (term748 _86426 q) = (term735 _86426 q).
Proof. exact (eq_refl (term748 _86426 q)). Qed.
Lemma lem3300647 {_86426 : Type'} : (term755 _86426) = (term746 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300646 _86426 q)). Qed.
Lemma lem3300648 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300649 {_86426 : Type'} : (term756 _86426) = (term757 _86426).
Proof. exact (MK_COMB (@lem3300648 _86426) (@lem3300647 _86426)). Qed.
Lemma lem3300650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300651 {_86426 : Type'} : (term758 _86426) = (term759 _86426).
Proof. exact (MK_COMB (@lem3300650) (@lem3300649 _86426)). Qed.
Lemma lem3300652 {_86426 : Type'} (q : _86426 -> Prop) : (term750 _86426 q) = (term740 _86426 q).
Proof. exact (eq_refl (term750 _86426 q)). Qed.
Lemma lem3300653 {_86426 : Type'} : (term760 _86426) = (term747 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300652 _86426 q)). Qed.
Lemma lem3300654 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300655 {_86426 : Type'} : (term761 _86426) = (term762 _86426).
Proof. exact (MK_COMB (@lem3300654 _86426) (@lem3300653 _86426)). Qed.
Lemma lem3300656 {_86426 : Type'} : (term745 _86426) = (term763 _86426).
Proof. exact (MK_COMB (@lem3300651 _86426) (@lem3300655 _86426)). Qed.
Lemma lem3300657 {_86426 : Type'} : ((term744 _86426) = (term745 _86426)) = ((term743 _86426) = (term763 _86426)).
Proof. exact (MK_COMB (@lem3300645 _86426) (@lem3300656 _86426)). Qed.
Lemma lem3300658 {_86426 : Type'} : (term743 _86426) = (term763 _86426).
Proof. exact (EQ_MP (@lem3300657 _86426) (@lem3300635 _86426)). Qed.
Lemma lem3300771 {_86426 : Type'} : (term442 _86426) = (term763 _86426).
Proof. exact (TRANS (@lem3300631 _86426) (@lem3300658 _86426)). Qed.
Lemma lem3300772 {_86426 : Type'} : (term446 _86426) = (term764 _86426).
Proof. exact (MK_COMB (@lem3300362 _86426) (@lem3300771 _86426)). Qed.
Lemma lem3300773 {_86426 : Type'} : (term451 _86426) = (term765 _86426).
Proof. exact (MK_COMB (@lem3299796 _86426) (@lem3300772 _86426)). Qed.
Lemma lem3300774 {_86426 : Type'} : (term456 _86426) = (term766 _86426).
Proof. exact (MK_COMB (@lem3299230 _86426) (@lem3300773 _86426)). Qed.
Lemma lem3300776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300777 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3300776 (_86426 -> Prop) P Q). Qed.
Lemma lem3300778 {_86426 : Type'} : (term506 _86426) = (term505 _86426).
Proof. exact (@lem3300777 _86426 (term507 _86426) (term508 _86426)). Qed.
Lemma lem3300779 {_86426 : Type'} (q : _86426 -> Prop) : (term509 _86426 q) = (term496 _86426 q).
Proof. exact (eq_refl (term509 _86426 q)). Qed.
Lemma lem3300780 {_86426 : Type'} : (term516 _86426) = (term507 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300779 _86426 q)). Qed.
Lemma lem3300781 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300782 {_86426 : Type'} : (term517 _86426) = (term518 _86426).
Proof. exact (MK_COMB (@lem3300781 _86426) (@lem3300780 _86426)). Qed.
Lemma lem3300783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300784 {_86426 : Type'} : (term519 _86426) = (term520 _86426).
Proof. exact (MK_COMB (@lem3300783) (@lem3300782 _86426)). Qed.
Lemma lem3300785 {_86426 : Type'} (q : _86426 -> Prop) : (term511 _86426 q) = (term501 _86426 q).
Proof. exact (eq_refl (term511 _86426 q)). Qed.
Lemma lem3300786 {_86426 : Type'} : (term521 _86426) = (term508 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300785 _86426 q)). Qed.
Lemma lem3300787 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300788 {_86426 : Type'} : (term522 _86426) = (term523 _86426).
Proof. exact (MK_COMB (@lem3300787 _86426) (@lem3300786 _86426)). Qed.
Lemma lem3300789 {_86426 : Type'} : (term506 _86426) = (term524 _86426).
Proof. exact (MK_COMB (@lem3300784 _86426) (@lem3300788 _86426)). Qed.
Lemma lem3300790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300791 {_86426 : Type'} : (term767 _86426) = (term768 _86426).
Proof. exact (MK_COMB (@lem3300790) (@lem3300789 _86426)). Qed.
Lemma lem3300792 {_86426 : Type'} (q : _86426 -> Prop) : (term509 _86426 q) = (term496 _86426 q).
Proof. exact (eq_refl (term509 _86426 q)). Qed.
Lemma lem3300793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300794 {_86426 : Type'} (q : _86426 -> Prop) : (term510 _86426 q) = (term498 _86426 q).
Proof. exact (MK_COMB (@lem3300793) (@lem3300792 _86426 q)). Qed.
Lemma lem3300795 {_86426 : Type'} (q : _86426 -> Prop) : (term511 _86426 q) = (term501 _86426 q).
Proof. exact (eq_refl (term511 _86426 q)). Qed.
Lemma lem3300796 {_86426 : Type'} (q : _86426 -> Prop) : (term512 _86426 q) = (term502 _86426 q).
Proof. exact (MK_COMB (@lem3300794 _86426 q) (@lem3300795 _86426 q)). Qed.
Lemma lem3300797 {_86426 : Type'} : (term513 _86426) = (term503 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300796 _86426 q)). Qed.
Lemma lem3300798 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300799 {_86426 : Type'} : (term505 _86426) = (term504 _86426).
Proof. exact (MK_COMB (@lem3300798 _86426) (@lem3300797 _86426)). Qed.
Lemma lem3300800 {_86426 : Type'} : ((term506 _86426) = (term505 _86426)) = ((term524 _86426) = (term504 _86426)).
Proof. exact (MK_COMB (@lem3300791 _86426) (@lem3300799 _86426)). Qed.
Lemma lem3300801 {_86426 : Type'} : (term524 _86426) = (term504 _86426).
Proof. exact (EQ_MP (@lem3300800 _86426) (@lem3300778 _86426)). Qed.
Lemma lem3300803 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300804 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3300803 (_86426 -> Prop) P Q). Qed.
Lemma lem3300805 {_86426 : Type'} (q : _86426 -> Prop) : (term484 _86426 q) = (term483 _86426 q).
Proof. exact (@lem3300804 _86426 (term485 _86426 q) (term486 _86426 q)). Qed.
Lemma lem3300806 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term487 _86426 q p) = (term472 _86426 q p).
Proof. exact (eq_refl (term487 _86426 q p)). Qed.
Lemma lem3300807 {_86426 : Type'} (q : _86426 -> Prop) : (term494 _86426 q) = (term485 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300806 _86426 q p)). Qed.
Lemma lem3300808 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300809 {_86426 : Type'} (q : _86426 -> Prop) : (term495 _86426 q) = (term496 _86426 q).
Proof. exact (MK_COMB (@lem3300808 _86426) (@lem3300807 _86426 q)). Qed.
Lemma lem3300810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300811 {_86426 : Type'} (q : _86426 -> Prop) : (term497 _86426 q) = (term498 _86426 q).
Proof. exact (MK_COMB (@lem3300810) (@lem3300809 _86426 q)). Qed.
Lemma lem3300812 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term489 _86426 q p) = (term477 _86426 q p).
Proof. exact (eq_refl (term489 _86426 q p)). Qed.
Lemma lem3300813 {_86426 : Type'} (q : _86426 -> Prop) : (term499 _86426 q) = (term486 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300812 _86426 q p)). Qed.
Lemma lem3300814 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300815 {_86426 : Type'} (q : _86426 -> Prop) : (term500 _86426 q) = (term501 _86426 q).
Proof. exact (MK_COMB (@lem3300814 _86426) (@lem3300813 _86426 q)). Qed.
Lemma lem3300816 {_86426 : Type'} (q : _86426 -> Prop) : (term484 _86426 q) = (term502 _86426 q).
Proof. exact (MK_COMB (@lem3300811 _86426 q) (@lem3300815 _86426 q)). Qed.
Lemma lem3300817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300818 {_86426 : Type'} (q : _86426 -> Prop) : (term769 _86426 q) = (term770 _86426 q).
Proof. exact (MK_COMB (@lem3300817) (@lem3300816 _86426 q)). Qed.
Lemma lem3300819 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term487 _86426 q p) = (term472 _86426 q p).
Proof. exact (eq_refl (term487 _86426 q p)). Qed.
Lemma lem3300820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300821 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term488 _86426 q p) = (term474 _86426 q p).
Proof. exact (MK_COMB (@lem3300820) (@lem3300819 _86426 q p)). Qed.
Lemma lem3300822 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term489 _86426 q p) = (term477 _86426 q p).
Proof. exact (eq_refl (term489 _86426 q p)). Qed.
Lemma lem3300823 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term490 _86426 q p) = (term478 _86426 q p).
Proof. exact (MK_COMB (@lem3300821 _86426 q p) (@lem3300822 _86426 q p)). Qed.
Lemma lem3300824 {_86426 : Type'} (q : _86426 -> Prop) : (term491 _86426 q) = (term479 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300823 _86426 q p)). Qed.
Lemma lem3300825 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300826 {_86426 : Type'} (q : _86426 -> Prop) : (term483 _86426 q) = (term480 _86426 q).
Proof. exact (MK_COMB (@lem3300825 _86426) (@lem3300824 _86426 q)). Qed.
Lemma lem3300827 {_86426 : Type'} (q : _86426 -> Prop) : ((term484 _86426 q) = (term483 _86426 q)) = ((term502 _86426 q) = (term480 _86426 q)).
Proof. exact (MK_COMB (@lem3300818 _86426 q) (@lem3300826 _86426 q)). Qed.
Lemma lem3300828 {_86426 : Type'} (q : _86426 -> Prop) : (term502 _86426 q) = (term480 _86426 q).
Proof. exact (EQ_MP (@lem3300827 _86426 q) (@lem3300805 _86426 q)). Qed.
Lemma lem3300830 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300831 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term458 _86426 P Q) = (term457 _86426 P Q).
Proof. exact (@lem3300830 _86426 P Q). Qed.
Lemma lem3300832 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term460 _86426 q p) = (term459 _86426 q p).
Proof. exact (@lem3300831 _86426 (term461 _86426 q p) (term462 _86426 q p)). Qed.
Lemma lem3300833 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term463 _86426 q p x) = (term298 _86426 q p x).
Proof. exact (eq_refl (term463 _86426 q p x)). Qed.
Lemma lem3300834 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term470 _86426 q p) = (term461 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3300833 _86426 q p x)). Qed.
Lemma lem3300835 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300836 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term471 _86426 q p) = (term472 _86426 q p).
Proof. exact (MK_COMB (@lem3300835 _86426) (@lem3300834 _86426 q p)). Qed.
Lemma lem3300837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300838 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term473 _86426 q p) = (term474 _86426 q p).
Proof. exact (MK_COMB (@lem3300837) (@lem3300836 _86426 q p)). Qed.
Lemma lem3300839 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term465 _86426 q p x) = (term295 _86426 q p x).
Proof. exact (eq_refl (term465 _86426 q p x)). Qed.
Lemma lem3300840 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term475 _86426 q p) = (term462 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3300839 _86426 q p x)). Qed.
Lemma lem3300841 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300842 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term476 _86426 q p) = (term477 _86426 q p).
Proof. exact (MK_COMB (@lem3300841 _86426) (@lem3300840 _86426 q p)). Qed.
Lemma lem3300843 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term460 _86426 q p) = (term478 _86426 q p).
Proof. exact (MK_COMB (@lem3300838 _86426 q p) (@lem3300842 _86426 q p)). Qed.
Lemma lem3300844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300845 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term771 _86426 q p) = (term772 _86426 q p).
Proof. exact (MK_COMB (@lem3300844) (@lem3300843 _86426 q p)). Qed.
Lemma lem3300846 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term463 _86426 q p x) = (term298 _86426 q p x).
Proof. exact (eq_refl (term463 _86426 q p x)). Qed.
Lemma lem3300847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300848 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term464 _86426 q p x) = (term300 _86426 q p x).
Proof. exact (MK_COMB (@lem3300847) (@lem3300846 _86426 q p x)). Qed.
Lemma lem3300849 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term465 _86426 q p x) = (term295 _86426 q p x).
Proof. exact (eq_refl (term465 _86426 q p x)). Qed.
Lemma lem3300850 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term466 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (MK_COMB (@lem3300848 _86426 q p x) (@lem3300849 _86426 q p x)). Qed.
Lemma lem3300851 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term467 _86426 q p) = (term311 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3300850 _86426 q p x)). Qed.
Lemma lem3300852 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300853 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term459 _86426 q p) = (term312 _86426 q p).
Proof. exact (MK_COMB (@lem3300852 _86426) (@lem3300851 _86426 q p)). Qed.
Lemma lem3300854 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : ((term460 _86426 q p) = (term459 _86426 q p)) = ((term478 _86426 q p) = (term312 _86426 q p)).
Proof. exact (MK_COMB (@lem3300845 _86426 q p) (@lem3300853 _86426 q p)). Qed.
Lemma lem3300855 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term478 _86426 q p) = (term312 _86426 q p).
Proof. exact (EQ_MP (@lem3300854 _86426 q p) (@lem3300832 _86426 q p)). Qed.
Lemma lem3300856 {_86426 : Type'} (q : _86426 -> Prop) : (term479 _86426 q) = (term319 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300855 _86426 q p)). Qed.
Lemma lem3300857 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300858 {_86426 : Type'} (q : _86426 -> Prop) : (term480 _86426 q) = (term320 _86426 q).
Proof. exact (MK_COMB (@lem3300857 _86426) (@lem3300856 _86426 q)). Qed.
Lemma lem3300859 {_86426 : Type'} (q : _86426 -> Prop) : (term502 _86426 q) = (term320 _86426 q).
Proof. exact (TRANS (@lem3300828 _86426 q) (@lem3300858 _86426 q)). Qed.
Lemma lem3300860 {_86426 : Type'} : (term503 _86426) = (term325 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300859 _86426 q)). Qed.
Lemma lem3300861 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300862 {_86426 : Type'} : (term504 _86426) = (term326 _86426).
Proof. exact (MK_COMB (@lem3300861 _86426) (@lem3300860 _86426)). Qed.
Lemma lem3300863 {_86426 : Type'} : (term524 _86426) = (term326 _86426).
Proof. exact (TRANS (@lem3300801 _86426) (@lem3300862 _86426)). Qed.
Lemma lem3300864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300865 {_86426 : Type'} : (term525 _86426) = (term454 _86426).
Proof. exact (MK_COMB (@lem3300864) (@lem3300863 _86426)). Qed.
Lemma lem3300867 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300868 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3300867 (_86426 -> Prop) P Q). Qed.
Lemma lem3300869 {_86426 : Type'} : (term593 _86426) = (term592 _86426).
Proof. exact (@lem3300868 _86426 (term594 _86426) (term595 _86426)). Qed.
Lemma lem3300870 {_86426 : Type'} (q : _86426 -> Prop) : (term596 _86426 q) = (term583 _86426 q).
Proof. exact (eq_refl (term596 _86426 q)). Qed.
Lemma lem3300871 {_86426 : Type'} : (term603 _86426) = (term594 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300870 _86426 q)). Qed.
Lemma lem3300872 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300873 {_86426 : Type'} : (term604 _86426) = (term605 _86426).
Proof. exact (MK_COMB (@lem3300872 _86426) (@lem3300871 _86426)). Qed.
Lemma lem3300874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300875 {_86426 : Type'} : (term606 _86426) = (term607 _86426).
Proof. exact (MK_COMB (@lem3300874) (@lem3300873 _86426)). Qed.
Lemma lem3300876 {_86426 : Type'} (q : _86426 -> Prop) : (term598 _86426 q) = (term588 _86426 q).
Proof. exact (eq_refl (term598 _86426 q)). Qed.
Lemma lem3300877 {_86426 : Type'} : (term608 _86426) = (term595 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300876 _86426 q)). Qed.
Lemma lem3300878 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300879 {_86426 : Type'} : (term609 _86426) = (term610 _86426).
Proof. exact (MK_COMB (@lem3300878 _86426) (@lem3300877 _86426)). Qed.
Lemma lem3300880 {_86426 : Type'} : (term593 _86426) = (term611 _86426).
Proof. exact (MK_COMB (@lem3300875 _86426) (@lem3300879 _86426)). Qed.
Lemma lem3300881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300882 {_86426 : Type'} : (term773 _86426) = (term774 _86426).
Proof. exact (MK_COMB (@lem3300881) (@lem3300880 _86426)). Qed.
Lemma lem3300883 {_86426 : Type'} (q : _86426 -> Prop) : (term596 _86426 q) = (term583 _86426 q).
Proof. exact (eq_refl (term596 _86426 q)). Qed.
Lemma lem3300884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300885 {_86426 : Type'} (q : _86426 -> Prop) : (term597 _86426 q) = (term585 _86426 q).
Proof. exact (MK_COMB (@lem3300884) (@lem3300883 _86426 q)). Qed.
Lemma lem3300886 {_86426 : Type'} (q : _86426 -> Prop) : (term598 _86426 q) = (term588 _86426 q).
Proof. exact (eq_refl (term598 _86426 q)). Qed.
Lemma lem3300887 {_86426 : Type'} (q : _86426 -> Prop) : (term599 _86426 q) = (term589 _86426 q).
Proof. exact (MK_COMB (@lem3300885 _86426 q) (@lem3300886 _86426 q)). Qed.
Lemma lem3300888 {_86426 : Type'} : (term600 _86426) = (term590 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300887 _86426 q)). Qed.
Lemma lem3300889 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300890 {_86426 : Type'} : (term592 _86426) = (term591 _86426).
Proof. exact (MK_COMB (@lem3300889 _86426) (@lem3300888 _86426)). Qed.
Lemma lem3300891 {_86426 : Type'} : ((term593 _86426) = (term592 _86426)) = ((term611 _86426) = (term591 _86426)).
Proof. exact (MK_COMB (@lem3300882 _86426) (@lem3300890 _86426)). Qed.
Lemma lem3300892 {_86426 : Type'} : (term611 _86426) = (term591 _86426).
Proof. exact (EQ_MP (@lem3300891 _86426) (@lem3300869 _86426)). Qed.
Lemma lem3300894 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300895 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3300894 (_86426 -> Prop) P Q). Qed.
Lemma lem3300896 {_86426 : Type'} (q : _86426 -> Prop) : (term571 _86426 q) = (term570 _86426 q).
Proof. exact (@lem3300895 _86426 (term572 _86426 q) (term573 _86426 q)). Qed.
Lemma lem3300897 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term574 _86426 q p) = (term561 _86426 p q).
Proof. exact (eq_refl (term574 _86426 q p)). Qed.
Lemma lem3300898 {_86426 : Type'} (q : _86426 -> Prop) : (term581 _86426 q) = (term572 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300897 _86426 p q)). Qed.
Lemma lem3300899 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300900 {_86426 : Type'} (q : _86426 -> Prop) : (term582 _86426 q) = (term583 _86426 q).
Proof. exact (MK_COMB (@lem3300899 _86426) (@lem3300898 _86426 q)). Qed.
Lemma lem3300901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300902 {_86426 : Type'} (q : _86426 -> Prop) : (term584 _86426 q) = (term585 _86426 q).
Proof. exact (MK_COMB (@lem3300901) (@lem3300900 _86426 q)). Qed.
Lemma lem3300903 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term576 _86426 q p) = (term566 _86426 p q).
Proof. exact (eq_refl (term576 _86426 q p)). Qed.
Lemma lem3300904 {_86426 : Type'} (q : _86426 -> Prop) : (term586 _86426 q) = (term573 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300903 _86426 p q)). Qed.
Lemma lem3300905 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300906 {_86426 : Type'} (q : _86426 -> Prop) : (term587 _86426 q) = (term588 _86426 q).
Proof. exact (MK_COMB (@lem3300905 _86426) (@lem3300904 _86426 q)). Qed.
Lemma lem3300907 {_86426 : Type'} (q : _86426 -> Prop) : (term571 _86426 q) = (term589 _86426 q).
Proof. exact (MK_COMB (@lem3300902 _86426 q) (@lem3300906 _86426 q)). Qed.
Lemma lem3300908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300909 {_86426 : Type'} (q : _86426 -> Prop) : (term775 _86426 q) = (term776 _86426 q).
Proof. exact (MK_COMB (@lem3300908) (@lem3300907 _86426 q)). Qed.
Lemma lem3300910 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term574 _86426 q p) = (term561 _86426 p q).
Proof. exact (eq_refl (term574 _86426 q p)). Qed.
Lemma lem3300911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300912 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term575 _86426 q p) = (term563 _86426 p q).
Proof. exact (MK_COMB (@lem3300911) (@lem3300910 _86426 p q)). Qed.
Lemma lem3300913 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term576 _86426 q p) = (term566 _86426 p q).
Proof. exact (eq_refl (term576 _86426 q p)). Qed.
Lemma lem3300914 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term577 _86426 q p) = (term567 _86426 p q).
Proof. exact (MK_COMB (@lem3300912 _86426 p q) (@lem3300913 _86426 p q)). Qed.
Lemma lem3300915 {_86426 : Type'} (q : _86426 -> Prop) : (term578 _86426 q) = (term568 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300914 _86426 p q)). Qed.
Lemma lem3300916 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300917 {_86426 : Type'} (q : _86426 -> Prop) : (term570 _86426 q) = (term569 _86426 q).
Proof. exact (MK_COMB (@lem3300916 _86426) (@lem3300915 _86426 q)). Qed.
Lemma lem3300918 {_86426 : Type'} (q : _86426 -> Prop) : ((term571 _86426 q) = (term570 _86426 q)) = ((term589 _86426 q) = (term569 _86426 q)).
Proof. exact (MK_COMB (@lem3300909 _86426 q) (@lem3300917 _86426 q)). Qed.
Lemma lem3300919 {_86426 : Type'} (q : _86426 -> Prop) : (term589 _86426 q) = (term569 _86426 q).
Proof. exact (EQ_MP (@lem3300918 _86426 q) (@lem3300896 _86426 q)). Qed.
Lemma lem3300921 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300922 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3300921 (_86426 -> Prop) P Q). Qed.
Lemma lem3300923 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term549 _86426 p q) = (term548 _86426 p q).
Proof. exact (@lem3300922 _86426 (term550 _86426 p q) (term551 _86426 p q)). Qed.
Lemma lem3300924 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term552 _86426 p q r) = (term539 _86426 p q r).
Proof. exact (eq_refl (term552 _86426 p q r)). Qed.
Lemma lem3300925 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term559 _86426 p q) = (term550 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3300924 _86426 p q r)). Qed.
Lemma lem3300926 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300927 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term560 _86426 p q) = (term561 _86426 p q).
Proof. exact (MK_COMB (@lem3300926 _86426) (@lem3300925 _86426 p q)). Qed.
Lemma lem3300928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300929 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term562 _86426 p q) = (term563 _86426 p q).
Proof. exact (MK_COMB (@lem3300928) (@lem3300927 _86426 p q)). Qed.
Lemma lem3300930 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term554 _86426 p q r) = (term544 _86426 p q r).
Proof. exact (eq_refl (term554 _86426 p q r)). Qed.
Lemma lem3300931 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term564 _86426 p q) = (term551 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3300930 _86426 p q r)). Qed.
Lemma lem3300932 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300933 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term565 _86426 p q) = (term566 _86426 p q).
Proof. exact (MK_COMB (@lem3300932 _86426) (@lem3300931 _86426 p q)). Qed.
Lemma lem3300934 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term549 _86426 p q) = (term567 _86426 p q).
Proof. exact (MK_COMB (@lem3300929 _86426 p q) (@lem3300933 _86426 p q)). Qed.
Lemma lem3300935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300936 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term777 _86426 p q) = (term778 _86426 p q).
Proof. exact (MK_COMB (@lem3300935) (@lem3300934 _86426 p q)). Qed.
Lemma lem3300937 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term552 _86426 p q r) = (term539 _86426 p q r).
Proof. exact (eq_refl (term552 _86426 p q r)). Qed.
Lemma lem3300938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300939 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term553 _86426 p q r) = (term541 _86426 p q r).
Proof. exact (MK_COMB (@lem3300938) (@lem3300937 _86426 p q r)). Qed.
Lemma lem3300940 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term554 _86426 p q r) = (term544 _86426 p q r).
Proof. exact (eq_refl (term554 _86426 p q r)). Qed.
Lemma lem3300941 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term555 _86426 p q r) = (term545 _86426 p q r).
Proof. exact (MK_COMB (@lem3300939 _86426 p q r) (@lem3300940 _86426 p q r)). Qed.
Lemma lem3300942 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term556 _86426 p q) = (term546 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3300941 _86426 p q r)). Qed.
Lemma lem3300943 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300944 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term548 _86426 p q) = (term547 _86426 p q).
Proof. exact (MK_COMB (@lem3300943 _86426) (@lem3300942 _86426 p q)). Qed.
Lemma lem3300945 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term549 _86426 p q) = (term548 _86426 p q)) = ((term567 _86426 p q) = (term547 _86426 p q)).
Proof. exact (MK_COMB (@lem3300936 _86426 p q) (@lem3300944 _86426 p q)). Qed.
Lemma lem3300946 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term567 _86426 p q) = (term547 _86426 p q).
Proof. exact (EQ_MP (@lem3300945 _86426 p q) (@lem3300923 _86426 p q)). Qed.
Lemma lem3300948 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300949 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term458 _86426 P Q) = (term457 _86426 P Q).
Proof. exact (@lem3300948 _86426 P Q). Qed.
Lemma lem3300950 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term527 _86426 p q r) = (term526 _86426 p q r).
Proof. exact (@lem3300949 _86426 (term528 _86426 p q r) (term529 _86426 p q r)). Qed.
Lemma lem3300951 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term530 _86426 p q r x) = (term341 _86426 p q r x).
Proof. exact (eq_refl (term530 _86426 p q r x)). Qed.
Lemma lem3300952 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term537 _86426 p q r) = (term528 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3300951 _86426 p q r x)). Qed.
Lemma lem3300953 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300954 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term538 _86426 p q r) = (term539 _86426 p q r).
Proof. exact (MK_COMB (@lem3300953 _86426) (@lem3300952 _86426 p q r)). Qed.
Lemma lem3300955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300956 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term540 _86426 p q r) = (term541 _86426 p q r).
Proof. exact (MK_COMB (@lem3300955) (@lem3300954 _86426 p q r)). Qed.
Lemma lem3300957 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term532 _86426 p q r x) = (term338 _86426 p q r x).
Proof. exact (eq_refl (term532 _86426 p q r x)). Qed.
Lemma lem3300958 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term542 _86426 p q r) = (term529 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3300957 _86426 p q r x)). Qed.
Lemma lem3300959 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300960 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term543 _86426 p q r) = (term544 _86426 p q r).
Proof. exact (MK_COMB (@lem3300959 _86426) (@lem3300958 _86426 p q r)). Qed.
Lemma lem3300961 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term527 _86426 p q r) = (term545 _86426 p q r).
Proof. exact (MK_COMB (@lem3300956 _86426 p q r) (@lem3300960 _86426 p q r)). Qed.
Lemma lem3300962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3300963 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term779 _86426 p q r) = (term780 _86426 p q r).
Proof. exact (MK_COMB (@lem3300962) (@lem3300961 _86426 p q r)). Qed.
Lemma lem3300964 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term530 _86426 p q r x) = (term341 _86426 p q r x).
Proof. exact (eq_refl (term530 _86426 p q r x)). Qed.
Lemma lem3300965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300966 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term531 _86426 p q r x) = (term343 _86426 p q r x).
Proof. exact (MK_COMB (@lem3300965) (@lem3300964 _86426 p q r x)). Qed.
Lemma lem3300967 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term532 _86426 p q r x) = (term338 _86426 p q r x).
Proof. exact (eq_refl (term532 _86426 p q r x)). Qed.
Lemma lem3300968 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term533 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (MK_COMB (@lem3300966 _86426 p q r x) (@lem3300967 _86426 p q r x)). Qed.
Lemma lem3300969 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term534 _86426 p q r) = (term352 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3300968 _86426 p q r x)). Qed.
Lemma lem3300970 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3300971 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term526 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (MK_COMB (@lem3300970 _86426) (@lem3300969 _86426 p q r)). Qed.
Lemma lem3300972 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : ((term527 _86426 p q r) = (term526 _86426 p q r)) = ((term545 _86426 p q r) = (term353 _86426 p q r)).
Proof. exact (MK_COMB (@lem3300963 _86426 p q r) (@lem3300971 _86426 p q r)). Qed.
Lemma lem3300973 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term545 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (EQ_MP (@lem3300972 _86426 p q r) (@lem3300950 _86426 p q r)). Qed.
Lemma lem3300974 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term546 _86426 p q) = (term358 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3300973 _86426 p q r)). Qed.
Lemma lem3300975 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300976 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term547 _86426 p q) = (term359 _86426 p q).
Proof. exact (MK_COMB (@lem3300975 _86426) (@lem3300974 _86426 p q)). Qed.
Lemma lem3300977 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term567 _86426 p q) = (term359 _86426 p q).
Proof. exact (TRANS (@lem3300946 _86426 p q) (@lem3300976 _86426 p q)). Qed.
Lemma lem3300978 {_86426 : Type'} (q : _86426 -> Prop) : (term568 _86426 q) = (term364 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3300977 _86426 p q)). Qed.
Lemma lem3300979 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300980 {_86426 : Type'} (q : _86426 -> Prop) : (term569 _86426 q) = (term365 _86426 q).
Proof. exact (MK_COMB (@lem3300979 _86426) (@lem3300978 _86426 q)). Qed.
Lemma lem3300981 {_86426 : Type'} (q : _86426 -> Prop) : (term589 _86426 q) = (term365 _86426 q).
Proof. exact (TRANS (@lem3300919 _86426 q) (@lem3300980 _86426 q)). Qed.
Lemma lem3300982 {_86426 : Type'} : (term590 _86426) = (term370 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300981 _86426 q)). Qed.
Lemma lem3300983 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300984 {_86426 : Type'} : (term591 _86426) = (term371 _86426).
Proof. exact (MK_COMB (@lem3300983 _86426) (@lem3300982 _86426)). Qed.
Lemma lem3300985 {_86426 : Type'} : (term611 _86426) = (term371 _86426).
Proof. exact (TRANS (@lem3300892 _86426) (@lem3300984 _86426)). Qed.
Lemma lem3300986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300987 {_86426 : Type'} : (term612 _86426) = (term449 _86426).
Proof. exact (MK_COMB (@lem3300986) (@lem3300985 _86426)). Qed.
Lemma lem3300989 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3300990 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3300989 (_86426 -> Prop) P Q). Qed.
Lemma lem3300991 {_86426 : Type'} : (term680 _86426) = (term679 _86426).
Proof. exact (@lem3300990 _86426 (term681 _86426) (term682 _86426)). Qed.
Lemma lem3300992 {_86426 : Type'} (q : _86426 -> Prop) : (term683 _86426 q) = (term670 _86426 q).
Proof. exact (eq_refl (term683 _86426 q)). Qed.
Lemma lem3300993 {_86426 : Type'} : (term690 _86426) = (term681 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300992 _86426 q)). Qed.
Lemma lem3300994 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3300995 {_86426 : Type'} : (term691 _86426) = (term692 _86426).
Proof. exact (MK_COMB (@lem3300994 _86426) (@lem3300993 _86426)). Qed.
Lemma lem3300996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3300997 {_86426 : Type'} : (term693 _86426) = (term694 _86426).
Proof. exact (MK_COMB (@lem3300996) (@lem3300995 _86426)). Qed.
Lemma lem3300998 {_86426 : Type'} (q : _86426 -> Prop) : (term685 _86426 q) = (term675 _86426 q).
Proof. exact (eq_refl (term685 _86426 q)). Qed.
Lemma lem3300999 {_86426 : Type'} : (term695 _86426) = (term682 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3300998 _86426 q)). Qed.
Lemma lem3301000 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301001 {_86426 : Type'} : (term696 _86426) = (term697 _86426).
Proof. exact (MK_COMB (@lem3301000 _86426) (@lem3300999 _86426)). Qed.
Lemma lem3301002 {_86426 : Type'} : (term680 _86426) = (term698 _86426).
Proof. exact (MK_COMB (@lem3300997 _86426) (@lem3301001 _86426)). Qed.
Lemma lem3301003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301004 {_86426 : Type'} : (term781 _86426) = (term782 _86426).
Proof. exact (MK_COMB (@lem3301003) (@lem3301002 _86426)). Qed.
Lemma lem3301005 {_86426 : Type'} (q : _86426 -> Prop) : (term683 _86426 q) = (term670 _86426 q).
Proof. exact (eq_refl (term683 _86426 q)). Qed.
Lemma lem3301006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301007 {_86426 : Type'} (q : _86426 -> Prop) : (term684 _86426 q) = (term672 _86426 q).
Proof. exact (MK_COMB (@lem3301006) (@lem3301005 _86426 q)). Qed.
Lemma lem3301008 {_86426 : Type'} (q : _86426 -> Prop) : (term685 _86426 q) = (term675 _86426 q).
Proof. exact (eq_refl (term685 _86426 q)). Qed.
Lemma lem3301009 {_86426 : Type'} (q : _86426 -> Prop) : (term686 _86426 q) = (term676 _86426 q).
Proof. exact (MK_COMB (@lem3301007 _86426 q) (@lem3301008 _86426 q)). Qed.
Lemma lem3301010 {_86426 : Type'} : (term687 _86426) = (term677 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301009 _86426 q)). Qed.
Lemma lem3301011 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301012 {_86426 : Type'} : (term679 _86426) = (term678 _86426).
Proof. exact (MK_COMB (@lem3301011 _86426) (@lem3301010 _86426)). Qed.
Lemma lem3301013 {_86426 : Type'} : ((term680 _86426) = (term679 _86426)) = ((term698 _86426) = (term678 _86426)).
Proof. exact (MK_COMB (@lem3301004 _86426) (@lem3301012 _86426)). Qed.
Lemma lem3301014 {_86426 : Type'} : (term698 _86426) = (term678 _86426).
Proof. exact (EQ_MP (@lem3301013 _86426) (@lem3300991 _86426)). Qed.
Lemma lem3301016 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301017 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301016 (_86426 -> Prop) P Q). Qed.
Lemma lem3301018 {_86426 : Type'} (q : _86426 -> Prop) : (term658 _86426 q) = (term657 _86426 q).
Proof. exact (@lem3301017 _86426 (term659 _86426 q) (term660 _86426 q)). Qed.
Lemma lem3301019 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term661 _86426 q p) = (term648 _86426 q p).
Proof. exact (eq_refl (term661 _86426 q p)). Qed.
Lemma lem3301020 {_86426 : Type'} (q : _86426 -> Prop) : (term668 _86426 q) = (term659 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301019 _86426 q p)). Qed.
Lemma lem3301021 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301022 {_86426 : Type'} (q : _86426 -> Prop) : (term669 _86426 q) = (term670 _86426 q).
Proof. exact (MK_COMB (@lem3301021 _86426) (@lem3301020 _86426 q)). Qed.
Lemma lem3301023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301024 {_86426 : Type'} (q : _86426 -> Prop) : (term671 _86426 q) = (term672 _86426 q).
Proof. exact (MK_COMB (@lem3301023) (@lem3301022 _86426 q)). Qed.
Lemma lem3301025 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term663 _86426 q p) = (term653 _86426 q p).
Proof. exact (eq_refl (term663 _86426 q p)). Qed.
Lemma lem3301026 {_86426 : Type'} (q : _86426 -> Prop) : (term673 _86426 q) = (term660 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301025 _86426 q p)). Qed.
Lemma lem3301027 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301028 {_86426 : Type'} (q : _86426 -> Prop) : (term674 _86426 q) = (term675 _86426 q).
Proof. exact (MK_COMB (@lem3301027 _86426) (@lem3301026 _86426 q)). Qed.
Lemma lem3301029 {_86426 : Type'} (q : _86426 -> Prop) : (term658 _86426 q) = (term676 _86426 q).
Proof. exact (MK_COMB (@lem3301024 _86426 q) (@lem3301028 _86426 q)). Qed.
Lemma lem3301030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301031 {_86426 : Type'} (q : _86426 -> Prop) : (term783 _86426 q) = (term784 _86426 q).
Proof. exact (MK_COMB (@lem3301030) (@lem3301029 _86426 q)). Qed.
Lemma lem3301032 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term661 _86426 q p) = (term648 _86426 q p).
Proof. exact (eq_refl (term661 _86426 q p)). Qed.
Lemma lem3301033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301034 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term662 _86426 q p) = (term650 _86426 q p).
Proof. exact (MK_COMB (@lem3301033) (@lem3301032 _86426 q p)). Qed.
Lemma lem3301035 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term663 _86426 q p) = (term653 _86426 q p).
Proof. exact (eq_refl (term663 _86426 q p)). Qed.
Lemma lem3301036 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term664 _86426 q p) = (term654 _86426 q p).
Proof. exact (MK_COMB (@lem3301034 _86426 q p) (@lem3301035 _86426 q p)). Qed.
Lemma lem3301037 {_86426 : Type'} (q : _86426 -> Prop) : (term665 _86426 q) = (term655 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301036 _86426 q p)). Qed.
Lemma lem3301038 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301039 {_86426 : Type'} (q : _86426 -> Prop) : (term657 _86426 q) = (term656 _86426 q).
Proof. exact (MK_COMB (@lem3301038 _86426) (@lem3301037 _86426 q)). Qed.
Lemma lem3301040 {_86426 : Type'} (q : _86426 -> Prop) : ((term658 _86426 q) = (term657 _86426 q)) = ((term676 _86426 q) = (term656 _86426 q)).
Proof. exact (MK_COMB (@lem3301031 _86426 q) (@lem3301039 _86426 q)). Qed.
Lemma lem3301041 {_86426 : Type'} (q : _86426 -> Prop) : (term676 _86426 q) = (term656 _86426 q).
Proof. exact (EQ_MP (@lem3301040 _86426 q) (@lem3301018 _86426 q)). Qed.
Lemma lem3301043 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301044 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301043 (_86426 -> Prop) P Q). Qed.
Lemma lem3301045 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term636 _86426 q p) = (term635 _86426 q p).
Proof. exact (@lem3301044 _86426 (term637 _86426 q p) (term638 _86426 q p)). Qed.
Lemma lem3301046 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term639 _86426 q p r) = (term626 _86426 q p r).
Proof. exact (eq_refl (term639 _86426 q p r)). Qed.
Lemma lem3301047 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term646 _86426 q p) = (term637 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301046 _86426 q p r)). Qed.
Lemma lem3301048 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301049 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term647 _86426 q p) = (term648 _86426 q p).
Proof. exact (MK_COMB (@lem3301048 _86426) (@lem3301047 _86426 q p)). Qed.
Lemma lem3301050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301051 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term649 _86426 q p) = (term650 _86426 q p).
Proof. exact (MK_COMB (@lem3301050) (@lem3301049 _86426 q p)). Qed.
Lemma lem3301052 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term641 _86426 q p r) = (term631 _86426 q p r).
Proof. exact (eq_refl (term641 _86426 q p r)). Qed.
Lemma lem3301053 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term651 _86426 q p) = (term638 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301052 _86426 q p r)). Qed.
Lemma lem3301054 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301055 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term652 _86426 q p) = (term653 _86426 q p).
Proof. exact (MK_COMB (@lem3301054 _86426) (@lem3301053 _86426 q p)). Qed.
Lemma lem3301056 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term636 _86426 q p) = (term654 _86426 q p).
Proof. exact (MK_COMB (@lem3301051 _86426 q p) (@lem3301055 _86426 q p)). Qed.
Lemma lem3301057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301058 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term785 _86426 q p) = (term786 _86426 q p).
Proof. exact (MK_COMB (@lem3301057) (@lem3301056 _86426 q p)). Qed.
Lemma lem3301059 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term639 _86426 q p r) = (term626 _86426 q p r).
Proof. exact (eq_refl (term639 _86426 q p r)). Qed.
Lemma lem3301060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301061 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term640 _86426 q p r) = (term628 _86426 q p r).
Proof. exact (MK_COMB (@lem3301060) (@lem3301059 _86426 q p r)). Qed.
Lemma lem3301062 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term641 _86426 q p r) = (term631 _86426 q p r).
Proof. exact (eq_refl (term641 _86426 q p r)). Qed.
Lemma lem3301063 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term642 _86426 q p r) = (term632 _86426 q p r).
Proof. exact (MK_COMB (@lem3301061 _86426 q p r) (@lem3301062 _86426 q p r)). Qed.
Lemma lem3301064 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term643 _86426 q p) = (term633 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301063 _86426 q p r)). Qed.
Lemma lem3301065 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301066 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term635 _86426 q p) = (term634 _86426 q p).
Proof. exact (MK_COMB (@lem3301065 _86426) (@lem3301064 _86426 q p)). Qed.
Lemma lem3301067 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : ((term636 _86426 q p) = (term635 _86426 q p)) = ((term654 _86426 q p) = (term634 _86426 q p)).
Proof. exact (MK_COMB (@lem3301058 _86426 q p) (@lem3301066 _86426 q p)). Qed.
Lemma lem3301068 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term654 _86426 q p) = (term634 _86426 q p).
Proof. exact (EQ_MP (@lem3301067 _86426 q p) (@lem3301045 _86426 q p)). Qed.
Lemma lem3301070 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301071 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term458 _86426 P Q) = (term457 _86426 P Q).
Proof. exact (@lem3301070 _86426 P Q). Qed.
Lemma lem3301072 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term614 _86426 q p r) = (term613 _86426 q p r).
Proof. exact (@lem3301071 _86426 (term615 _86426 q p r) (term616 _86426 q p r)). Qed.
Lemma lem3301073 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term617 _86426 q p r x) = (term378 _86426 q p r x).
Proof. exact (eq_refl (term617 _86426 q p r x)). Qed.
Lemma lem3301074 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term624 _86426 q p r) = (term615 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3301073 _86426 q p r x)). Qed.
Lemma lem3301075 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301076 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term625 _86426 q p r) = (term626 _86426 q p r).
Proof. exact (MK_COMB (@lem3301075 _86426) (@lem3301074 _86426 q p r)). Qed.
Lemma lem3301077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301078 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term627 _86426 q p r) = (term628 _86426 q p r).
Proof. exact (MK_COMB (@lem3301077) (@lem3301076 _86426 q p r)). Qed.
Lemma lem3301079 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term619 _86426 q p r x) = (term375 _86426 q p r x).
Proof. exact (eq_refl (term619 _86426 q p r x)). Qed.
Lemma lem3301080 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term629 _86426 q p r) = (term616 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3301079 _86426 q p r x)). Qed.
Lemma lem3301081 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301082 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term630 _86426 q p r) = (term631 _86426 q p r).
Proof. exact (MK_COMB (@lem3301081 _86426) (@lem3301080 _86426 q p r)). Qed.
Lemma lem3301083 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term614 _86426 q p r) = (term632 _86426 q p r).
Proof. exact (MK_COMB (@lem3301078 _86426 q p r) (@lem3301082 _86426 q p r)). Qed.
Lemma lem3301084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301085 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term787 _86426 q p r) = (term788 _86426 q p r).
Proof. exact (MK_COMB (@lem3301084) (@lem3301083 _86426 q p r)). Qed.
Lemma lem3301086 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term617 _86426 q p r x) = (term378 _86426 q p r x).
Proof. exact (eq_refl (term617 _86426 q p r x)). Qed.
Lemma lem3301087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301088 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term618 _86426 q p r x) = (term380 _86426 q p r x).
Proof. exact (MK_COMB (@lem3301087) (@lem3301086 _86426 q p r x)). Qed.
Lemma lem3301089 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term619 _86426 q p r x) = (term375 _86426 q p r x).
Proof. exact (eq_refl (term619 _86426 q p r x)). Qed.
Lemma lem3301090 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term620 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (MK_COMB (@lem3301088 _86426 q p r x) (@lem3301089 _86426 q p r x)). Qed.
Lemma lem3301091 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term621 _86426 q p r) = (term389 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3301090 _86426 q p r x)). Qed.
Lemma lem3301092 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301093 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term613 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (MK_COMB (@lem3301092 _86426) (@lem3301091 _86426 q p r)). Qed.
Lemma lem3301094 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : ((term614 _86426 q p r) = (term613 _86426 q p r)) = ((term632 _86426 q p r) = (term390 _86426 q p r)).
Proof. exact (MK_COMB (@lem3301085 _86426 q p r) (@lem3301093 _86426 q p r)). Qed.
Lemma lem3301095 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term632 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (EQ_MP (@lem3301094 _86426 q p r) (@lem3301072 _86426 q p r)). Qed.
Lemma lem3301096 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term633 _86426 q p) = (term395 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301095 _86426 q p r)). Qed.
Lemma lem3301097 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301098 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term634 _86426 q p) = (term396 _86426 q p).
Proof. exact (MK_COMB (@lem3301097 _86426) (@lem3301096 _86426 q p)). Qed.
Lemma lem3301099 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term654 _86426 q p) = (term396 _86426 q p).
Proof. exact (TRANS (@lem3301068 _86426 q p) (@lem3301098 _86426 q p)). Qed.
Lemma lem3301100 {_86426 : Type'} (q : _86426 -> Prop) : (term655 _86426 q) = (term401 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301099 _86426 q p)). Qed.
Lemma lem3301101 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301102 {_86426 : Type'} (q : _86426 -> Prop) : (term656 _86426 q) = (term402 _86426 q).
Proof. exact (MK_COMB (@lem3301101 _86426) (@lem3301100 _86426 q)). Qed.
Lemma lem3301103 {_86426 : Type'} (q : _86426 -> Prop) : (term676 _86426 q) = (term402 _86426 q).
Proof. exact (TRANS (@lem3301041 _86426 q) (@lem3301102 _86426 q)). Qed.
Lemma lem3301104 {_86426 : Type'} : (term677 _86426) = (term407 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301103 _86426 q)). Qed.
Lemma lem3301105 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301106 {_86426 : Type'} : (term678 _86426) = (term408 _86426).
Proof. exact (MK_COMB (@lem3301105 _86426) (@lem3301104 _86426)). Qed.
Lemma lem3301107 {_86426 : Type'} : (term698 _86426) = (term408 _86426).
Proof. exact (TRANS (@lem3301014 _86426) (@lem3301106 _86426)). Qed.
Lemma lem3301108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301109 {_86426 : Type'} : (term699 _86426) = (term444 _86426).
Proof. exact (MK_COMB (@lem3301108) (@lem3301107 _86426)). Qed.
Lemma lem3301111 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301112 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301111 (_86426 -> Prop) P Q). Qed.
Lemma lem3301113 {_86426 : Type'} : (term745 _86426) = (term744 _86426).
Proof. exact (@lem3301112 _86426 (term746 _86426) (term747 _86426)). Qed.
Lemma lem3301114 {_86426 : Type'} (q : _86426 -> Prop) : (term748 _86426 q) = (term735 _86426 q).
Proof. exact (eq_refl (term748 _86426 q)). Qed.
Lemma lem3301115 {_86426 : Type'} : (term755 _86426) = (term746 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301114 _86426 q)). Qed.
Lemma lem3301116 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301117 {_86426 : Type'} : (term756 _86426) = (term757 _86426).
Proof. exact (MK_COMB (@lem3301116 _86426) (@lem3301115 _86426)). Qed.
Lemma lem3301118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301119 {_86426 : Type'} : (term758 _86426) = (term759 _86426).
Proof. exact (MK_COMB (@lem3301118) (@lem3301117 _86426)). Qed.
Lemma lem3301120 {_86426 : Type'} (q : _86426 -> Prop) : (term750 _86426 q) = (term740 _86426 q).
Proof. exact (eq_refl (term750 _86426 q)). Qed.
Lemma lem3301121 {_86426 : Type'} : (term760 _86426) = (term747 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301120 _86426 q)). Qed.
Lemma lem3301122 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301123 {_86426 : Type'} : (term761 _86426) = (term762 _86426).
Proof. exact (MK_COMB (@lem3301122 _86426) (@lem3301121 _86426)). Qed.
Lemma lem3301124 {_86426 : Type'} : (term745 _86426) = (term763 _86426).
Proof. exact (MK_COMB (@lem3301119 _86426) (@lem3301123 _86426)). Qed.
Lemma lem3301125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301126 {_86426 : Type'} : (term789 _86426) = (term790 _86426).
Proof. exact (MK_COMB (@lem3301125) (@lem3301124 _86426)). Qed.
Lemma lem3301127 {_86426 : Type'} (q : _86426 -> Prop) : (term748 _86426 q) = (term735 _86426 q).
Proof. exact (eq_refl (term748 _86426 q)). Qed.
Lemma lem3301128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301129 {_86426 : Type'} (q : _86426 -> Prop) : (term749 _86426 q) = (term737 _86426 q).
Proof. exact (MK_COMB (@lem3301128) (@lem3301127 _86426 q)). Qed.
Lemma lem3301130 {_86426 : Type'} (q : _86426 -> Prop) : (term750 _86426 q) = (term740 _86426 q).
Proof. exact (eq_refl (term750 _86426 q)). Qed.
Lemma lem3301131 {_86426 : Type'} (q : _86426 -> Prop) : (term751 _86426 q) = (term741 _86426 q).
Proof. exact (MK_COMB (@lem3301129 _86426 q) (@lem3301130 _86426 q)). Qed.
Lemma lem3301132 {_86426 : Type'} : (term752 _86426) = (term742 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301131 _86426 q)). Qed.
Lemma lem3301133 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301134 {_86426 : Type'} : (term744 _86426) = (term743 _86426).
Proof. exact (MK_COMB (@lem3301133 _86426) (@lem3301132 _86426)). Qed.
Lemma lem3301135 {_86426 : Type'} : ((term745 _86426) = (term744 _86426)) = ((term763 _86426) = (term743 _86426)).
Proof. exact (MK_COMB (@lem3301126 _86426) (@lem3301134 _86426)). Qed.
Lemma lem3301136 {_86426 : Type'} : (term763 _86426) = (term743 _86426).
Proof. exact (EQ_MP (@lem3301135 _86426) (@lem3301113 _86426)). Qed.
Lemma lem3301138 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301139 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301138 (_86426 -> Prop) P Q). Qed.
Lemma lem3301140 {_86426 : Type'} (q : _86426 -> Prop) : (term723 _86426 q) = (term722 _86426 q).
Proof. exact (@lem3301139 _86426 (term724 _86426 q) (term725 _86426 q)). Qed.
Lemma lem3301141 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term726 _86426 q p) = (term713 _86426 p q).
Proof. exact (eq_refl (term726 _86426 q p)). Qed.
Lemma lem3301142 {_86426 : Type'} (q : _86426 -> Prop) : (term733 _86426 q) = (term724 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301141 _86426 p q)). Qed.
Lemma lem3301143 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301144 {_86426 : Type'} (q : _86426 -> Prop) : (term734 _86426 q) = (term735 _86426 q).
Proof. exact (MK_COMB (@lem3301143 _86426) (@lem3301142 _86426 q)). Qed.
Lemma lem3301145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301146 {_86426 : Type'} (q : _86426 -> Prop) : (term736 _86426 q) = (term737 _86426 q).
Proof. exact (MK_COMB (@lem3301145) (@lem3301144 _86426 q)). Qed.
Lemma lem3301147 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term728 _86426 q p) = (term718 _86426 p q).
Proof. exact (eq_refl (term728 _86426 q p)). Qed.
Lemma lem3301148 {_86426 : Type'} (q : _86426 -> Prop) : (term738 _86426 q) = (term725 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301147 _86426 p q)). Qed.
Lemma lem3301149 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301150 {_86426 : Type'} (q : _86426 -> Prop) : (term739 _86426 q) = (term740 _86426 q).
Proof. exact (MK_COMB (@lem3301149 _86426) (@lem3301148 _86426 q)). Qed.
Lemma lem3301151 {_86426 : Type'} (q : _86426 -> Prop) : (term723 _86426 q) = (term741 _86426 q).
Proof. exact (MK_COMB (@lem3301146 _86426 q) (@lem3301150 _86426 q)). Qed.
Lemma lem3301152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301153 {_86426 : Type'} (q : _86426 -> Prop) : (term791 _86426 q) = (term792 _86426 q).
Proof. exact (MK_COMB (@lem3301152) (@lem3301151 _86426 q)). Qed.
Lemma lem3301154 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term726 _86426 q p) = (term713 _86426 p q).
Proof. exact (eq_refl (term726 _86426 q p)). Qed.
Lemma lem3301155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301156 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term727 _86426 q p) = (term715 _86426 p q).
Proof. exact (MK_COMB (@lem3301155) (@lem3301154 _86426 p q)). Qed.
Lemma lem3301157 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term728 _86426 q p) = (term718 _86426 p q).
Proof. exact (eq_refl (term728 _86426 q p)). Qed.
Lemma lem3301158 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term729 _86426 q p) = (term719 _86426 p q).
Proof. exact (MK_COMB (@lem3301156 _86426 p q) (@lem3301157 _86426 p q)). Qed.
Lemma lem3301159 {_86426 : Type'} (q : _86426 -> Prop) : (term730 _86426 q) = (term720 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301158 _86426 p q)). Qed.
Lemma lem3301160 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301161 {_86426 : Type'} (q : _86426 -> Prop) : (term722 _86426 q) = (term721 _86426 q).
Proof. exact (MK_COMB (@lem3301160 _86426) (@lem3301159 _86426 q)). Qed.
Lemma lem3301162 {_86426 : Type'} (q : _86426 -> Prop) : ((term723 _86426 q) = (term722 _86426 q)) = ((term741 _86426 q) = (term721 _86426 q)).
Proof. exact (MK_COMB (@lem3301153 _86426 q) (@lem3301161 _86426 q)). Qed.
Lemma lem3301163 {_86426 : Type'} (q : _86426 -> Prop) : (term741 _86426 q) = (term721 _86426 q).
Proof. exact (EQ_MP (@lem3301162 _86426 q) (@lem3301140 _86426 q)). Qed.
Lemma lem3301165 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301166 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term458 _86426 P Q) = (term457 _86426 P Q).
Proof. exact (@lem3301165 _86426 P Q). Qed.
Lemma lem3301167 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term701 _86426 p q) = (term700 _86426 p q).
Proof. exact (@lem3301166 _86426 (term702 _86426 p q) (term703 _86426 p q)). Qed.
Lemma lem3301168 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term704 _86426 p q x) = (term418 _86426 p q x).
Proof. exact (eq_refl (term704 _86426 p q x)). Qed.
Lemma lem3301169 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term711 _86426 p q) = (term702 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301168 _86426 p q x)). Qed.
Lemma lem3301170 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301171 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term712 _86426 p q) = (term713 _86426 p q).
Proof. exact (MK_COMB (@lem3301170 _86426) (@lem3301169 _86426 p q)). Qed.
Lemma lem3301172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301173 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term714 _86426 p q) = (term715 _86426 p q).
Proof. exact (MK_COMB (@lem3301172) (@lem3301171 _86426 p q)). Qed.
Lemma lem3301174 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term706 _86426 p q x) = (term415 _86426 p q x).
Proof. exact (eq_refl (term706 _86426 p q x)). Qed.
Lemma lem3301175 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term716 _86426 p q) = (term703 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301174 _86426 p q x)). Qed.
Lemma lem3301176 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301177 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term717 _86426 p q) = (term718 _86426 p q).
Proof. exact (MK_COMB (@lem3301176 _86426) (@lem3301175 _86426 p q)). Qed.
Lemma lem3301178 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term701 _86426 p q) = (term719 _86426 p q).
Proof. exact (MK_COMB (@lem3301173 _86426 p q) (@lem3301177 _86426 p q)). Qed.
Lemma lem3301179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301180 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term793 _86426 p q) = (term794 _86426 p q).
Proof. exact (MK_COMB (@lem3301179) (@lem3301178 _86426 p q)). Qed.
Lemma lem3301181 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term704 _86426 p q x) = (term418 _86426 p q x).
Proof. exact (eq_refl (term704 _86426 p q x)). Qed.
Lemma lem3301182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301183 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term705 _86426 p q x) = (term420 _86426 p q x).
Proof. exact (MK_COMB (@lem3301182) (@lem3301181 _86426 p q x)). Qed.
Lemma lem3301184 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term706 _86426 p q x) = (term415 _86426 p q x).
Proof. exact (eq_refl (term706 _86426 p q x)). Qed.
Lemma lem3301185 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term707 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (MK_COMB (@lem3301183 _86426 p q x) (@lem3301184 _86426 p q x)). Qed.
Lemma lem3301186 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term708 _86426 p q) = (term429 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301185 _86426 p q x)). Qed.
Lemma lem3301187 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301188 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term700 _86426 p q) = (term430 _86426 p q).
Proof. exact (MK_COMB (@lem3301187 _86426) (@lem3301186 _86426 p q)). Qed.
Lemma lem3301189 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term701 _86426 p q) = (term700 _86426 p q)) = ((term719 _86426 p q) = (term430 _86426 p q)).
Proof. exact (MK_COMB (@lem3301180 _86426 p q) (@lem3301188 _86426 p q)). Qed.
Lemma lem3301190 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term719 _86426 p q) = (term430 _86426 p q).
Proof. exact (EQ_MP (@lem3301189 _86426 p q) (@lem3301167 _86426 p q)). Qed.
Lemma lem3301191 {_86426 : Type'} (q : _86426 -> Prop) : (term720 _86426 q) = (term435 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301190 _86426 p q)). Qed.
Lemma lem3301192 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301193 {_86426 : Type'} (q : _86426 -> Prop) : (term721 _86426 q) = (term436 _86426 q).
Proof. exact (MK_COMB (@lem3301192 _86426) (@lem3301191 _86426 q)). Qed.
Lemma lem3301194 {_86426 : Type'} (q : _86426 -> Prop) : (term741 _86426 q) = (term436 _86426 q).
Proof. exact (TRANS (@lem3301163 _86426 q) (@lem3301193 _86426 q)). Qed.
Lemma lem3301195 {_86426 : Type'} : (term742 _86426) = (term441 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301194 _86426 q)). Qed.
Lemma lem3301196 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301197 {_86426 : Type'} : (term743 _86426) = (term442 _86426).
Proof. exact (MK_COMB (@lem3301196 _86426) (@lem3301195 _86426)). Qed.
Lemma lem3301198 {_86426 : Type'} : (term763 _86426) = (term442 _86426).
Proof. exact (TRANS (@lem3301136 _86426) (@lem3301197 _86426)). Qed.
Lemma lem3301199 {_86426 : Type'} : (term764 _86426) = (term446 _86426).
Proof. exact (MK_COMB (@lem3301109 _86426) (@lem3301198 _86426)). Qed.
Lemma lem3301201 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301202 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301201 (_86426 -> Prop) P Q). Qed.
Lemma lem3301203 {_86426 : Type'} : (term795 _86426) = (term796 _86426).
Proof. exact (@lem3301202 _86426 (term407 _86426) (term441 _86426)). Qed.
Lemma lem3301204 {_86426 : Type'} (q : _86426 -> Prop) : (term797 _86426 q) = (term402 _86426 q).
Proof. exact (eq_refl (term797 _86426 q)). Qed.
Lemma lem3301205 {_86426 : Type'} : (term798 _86426) = (term407 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301204 _86426 q)). Qed.
Lemma lem3301206 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301207 {_86426 : Type'} : (term799 _86426) = (term408 _86426).
Proof. exact (MK_COMB (@lem3301206 _86426) (@lem3301205 _86426)). Qed.
Lemma lem3301208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301209 {_86426 : Type'} : (term800 _86426) = (term444 _86426).
Proof. exact (MK_COMB (@lem3301208) (@lem3301207 _86426)). Qed.
Lemma lem3301210 {_86426 : Type'} (q : _86426 -> Prop) : (term801 _86426 q) = (term436 _86426 q).
Proof. exact (eq_refl (term801 _86426 q)). Qed.
Lemma lem3301211 {_86426 : Type'} : (term802 _86426) = (term441 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301210 _86426 q)). Qed.
Lemma lem3301212 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301213 {_86426 : Type'} : (term803 _86426) = (term442 _86426).
Proof. exact (MK_COMB (@lem3301212 _86426) (@lem3301211 _86426)). Qed.
Lemma lem3301214 {_86426 : Type'} : (term795 _86426) = (term446 _86426).
Proof. exact (MK_COMB (@lem3301209 _86426) (@lem3301213 _86426)). Qed.
Lemma lem3301215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301216 {_86426 : Type'} : (term804 _86426) = (term805 _86426).
Proof. exact (MK_COMB (@lem3301215) (@lem3301214 _86426)). Qed.
Lemma lem3301217 {_86426 : Type'} (q : _86426 -> Prop) : (term797 _86426 q) = (term402 _86426 q).
Proof. exact (eq_refl (term797 _86426 q)). Qed.
Lemma lem3301218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301219 {_86426 : Type'} (q : _86426 -> Prop) : (term806 _86426 q) = (term807 _86426 q).
Proof. exact (MK_COMB (@lem3301218) (@lem3301217 _86426 q)). Qed.
Lemma lem3301220 {_86426 : Type'} (q : _86426 -> Prop) : (term801 _86426 q) = (term436 _86426 q).
Proof. exact (eq_refl (term801 _86426 q)). Qed.
Lemma lem3301221 {_86426 : Type'} (q : _86426 -> Prop) : (term808 _86426 q) = (term809 _86426 q).
Proof. exact (MK_COMB (@lem3301219 _86426 q) (@lem3301220 _86426 q)). Qed.
Lemma lem3301222 {_86426 : Type'} : (term810 _86426) = (term811 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301221 _86426 q)). Qed.
Lemma lem3301223 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301224 {_86426 : Type'} : (term796 _86426) = (term812 _86426).
Proof. exact (MK_COMB (@lem3301223 _86426) (@lem3301222 _86426)). Qed.
Lemma lem3301225 {_86426 : Type'} : ((term795 _86426) = (term796 _86426)) = ((term446 _86426) = (term812 _86426)).
Proof. exact (MK_COMB (@lem3301216 _86426) (@lem3301224 _86426)). Qed.
Lemma lem3301226 {_86426 : Type'} : (term446 _86426) = (term812 _86426).
Proof. exact (EQ_MP (@lem3301225 _86426) (@lem3301203 _86426)). Qed.
Lemma lem3301228 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301229 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301228 (_86426 -> Prop) P Q). Qed.
Lemma lem3301230 {_86426 : Type'} (q : _86426 -> Prop) : (term813 _86426 q) = (term814 _86426 q).
Proof. exact (@lem3301229 _86426 (term401 _86426 q) (term435 _86426 q)). Qed.
Lemma lem3301231 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term815 _86426 q p) = (term396 _86426 q p).
Proof. exact (eq_refl (term815 _86426 q p)). Qed.
Lemma lem3301232 {_86426 : Type'} (q : _86426 -> Prop) : (term816 _86426 q) = (term401 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301231 _86426 q p)). Qed.
Lemma lem3301233 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301234 {_86426 : Type'} (q : _86426 -> Prop) : (term817 _86426 q) = (term402 _86426 q).
Proof. exact (MK_COMB (@lem3301233 _86426) (@lem3301232 _86426 q)). Qed.
Lemma lem3301235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301236 {_86426 : Type'} (q : _86426 -> Prop) : (term818 _86426 q) = (term807 _86426 q).
Proof. exact (MK_COMB (@lem3301235) (@lem3301234 _86426 q)). Qed.
Lemma lem3301237 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term819 _86426 q p) = (term430 _86426 p q).
Proof. exact (eq_refl (term819 _86426 q p)). Qed.
Lemma lem3301238 {_86426 : Type'} (q : _86426 -> Prop) : (term820 _86426 q) = (term435 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301237 _86426 p q)). Qed.
Lemma lem3301239 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301240 {_86426 : Type'} (q : _86426 -> Prop) : (term821 _86426 q) = (term436 _86426 q).
Proof. exact (MK_COMB (@lem3301239 _86426) (@lem3301238 _86426 q)). Qed.
Lemma lem3301241 {_86426 : Type'} (q : _86426 -> Prop) : (term813 _86426 q) = (term809 _86426 q).
Proof. exact (MK_COMB (@lem3301236 _86426 q) (@lem3301240 _86426 q)). Qed.
Lemma lem3301242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301243 {_86426 : Type'} (q : _86426 -> Prop) : (term822 _86426 q) = (term823 _86426 q).
Proof. exact (MK_COMB (@lem3301242) (@lem3301241 _86426 q)). Qed.
Lemma lem3301244 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term815 _86426 q p) = (term396 _86426 q p).
Proof. exact (eq_refl (term815 _86426 q p)). Qed.
Lemma lem3301245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301246 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term824 _86426 q p) = (term825 _86426 q p).
Proof. exact (MK_COMB (@lem3301245) (@lem3301244 _86426 q p)). Qed.
Lemma lem3301247 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term819 _86426 q p) = (term430 _86426 p q).
Proof. exact (eq_refl (term819 _86426 q p)). Qed.
Lemma lem3301248 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term826 _86426 q p) = (term827 _86426 p q).
Proof. exact (MK_COMB (@lem3301246 _86426 q p) (@lem3301247 _86426 p q)). Qed.
Lemma lem3301249 {_86426 : Type'} (q : _86426 -> Prop) : (term828 _86426 q) = (term829 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301248 _86426 p q)). Qed.
Lemma lem3301250 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301251 {_86426 : Type'} (q : _86426 -> Prop) : (term814 _86426 q) = (term830 _86426 q).
Proof. exact (MK_COMB (@lem3301250 _86426) (@lem3301249 _86426 q)). Qed.
Lemma lem3301252 {_86426 : Type'} (q : _86426 -> Prop) : ((term813 _86426 q) = (term814 _86426 q)) = ((term809 _86426 q) = (term830 _86426 q)).
Proof. exact (MK_COMB (@lem3301243 _86426 q) (@lem3301251 _86426 q)). Qed.
Lemma lem3301253 {_86426 : Type'} (q : _86426 -> Prop) : (term809 _86426 q) = (term830 _86426 q).
Proof. exact (EQ_MP (@lem3301252 _86426 q) (@lem3301230 _86426 q)). Qed.
Lemma lem3301257 {A : Type'} (P : A -> Prop) (Q : Prop) : (term831 A P Q) = (term832 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3301258 {_86426 : Type'} (P : type686 _86426) (Q : Prop) : (term833 _86426 P Q) = (term834 _86426 P Q).
Proof. exact (@lem3301257 (_86426 -> Prop) P Q). Qed.
Lemma lem3301259 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term835 _86426 p q) = (term836 _86426 p q).
Proof. exact (@lem3301258 _86426 (term395 _86426 q p) (term430 _86426 p q)). Qed.
Lemma lem3301260 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term837 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (eq_refl (term837 _86426 q p r)). Qed.
Lemma lem3301261 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term838 _86426 q p) = (term395 _86426 q p).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301260 _86426 q p r)). Qed.
Lemma lem3301262 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301263 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term839 _86426 q p) = (term396 _86426 q p).
Proof. exact (MK_COMB (@lem3301262 _86426) (@lem3301261 _86426 q p)). Qed.
Lemma lem3301264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301265 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term840 _86426 q p) = (term825 _86426 q p).
Proof. exact (MK_COMB (@lem3301264) (@lem3301263 _86426 q p)). Qed.
Lemma lem3301266 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term430 _86426 p q) = (term430 _86426 p q).
Proof. exact (eq_refl (term430 _86426 p q)). Qed.
Lemma lem3301267 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term835 _86426 p q) = (term827 _86426 p q).
Proof. exact (MK_COMB (@lem3301265 _86426 q p) (@lem3301266 _86426 p q)). Qed.
Lemma lem3301268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301269 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term841 _86426 p q) = (term842 _86426 p q).
Proof. exact (MK_COMB (@lem3301268) (@lem3301267 _86426 p q)). Qed.
Lemma lem3301270 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term837 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (eq_refl (term837 _86426 q p r)). Qed.
Lemma lem3301271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301272 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term843 _86426 q p r) = (term844 _86426 q p r).
Proof. exact (MK_COMB (@lem3301271) (@lem3301270 _86426 q p r)). Qed.
Lemma lem3301273 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term430 _86426 p q) = (term430 _86426 p q).
Proof. exact (eq_refl (term430 _86426 p q)). Qed.
Lemma lem3301274 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term845 _86426 r p q) = (term846 _86426 r p q).
Proof. exact (MK_COMB (@lem3301272 _86426 q p r) (@lem3301273 _86426 p q)). Qed.
Lemma lem3301275 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term847 _86426 p q) = (term848 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301274 _86426 r p q)). Qed.
Lemma lem3301276 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301277 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term836 _86426 p q) = (term849 _86426 p q).
Proof. exact (MK_COMB (@lem3301276 _86426) (@lem3301275 _86426 p q)). Qed.
Lemma lem3301278 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term835 _86426 p q) = (term836 _86426 p q)) = ((term827 _86426 p q) = (term849 _86426 p q)).
Proof. exact (MK_COMB (@lem3301269 _86426 p q) (@lem3301277 _86426 p q)). Qed.
Lemma lem3301279 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term827 _86426 p q) = (term849 _86426 p q).
Proof. exact (EQ_MP (@lem3301278 _86426 p q) (@lem3301259 _86426 p q)). Qed.
Lemma lem3301281 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301282 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term458 _86426 P Q) = (term457 _86426 P Q).
Proof. exact (@lem3301281 _86426 P Q). Qed.
Lemma lem3301283 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term850 _86426 r p q) = (term851 _86426 r p q).
Proof. exact (@lem3301282 _86426 (term389 _86426 q p r) (term429 _86426 p q)). Qed.
Lemma lem3301284 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term852 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (eq_refl (term852 _86426 q p r x)). Qed.
Lemma lem3301285 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term853 _86426 q p r) = (term389 _86426 q p r).
Proof. exact (fun_ext (fun x : _86426 => @lem3301284 _86426 q p r x)). Qed.
Lemma lem3301286 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301287 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term854 _86426 q p r) = (term390 _86426 q p r).
Proof. exact (MK_COMB (@lem3301286 _86426) (@lem3301285 _86426 q p r)). Qed.
Lemma lem3301288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301289 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) : (term855 _86426 q p r) = (term844 _86426 q p r).
Proof. exact (MK_COMB (@lem3301288) (@lem3301287 _86426 q p r)). Qed.
Lemma lem3301290 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term856 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (eq_refl (term856 _86426 p q x)). Qed.
Lemma lem3301291 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term857 _86426 p q) = (term429 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301290 _86426 p q x)). Qed.
Lemma lem3301292 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301293 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term858 _86426 p q) = (term430 _86426 p q).
Proof. exact (MK_COMB (@lem3301292 _86426) (@lem3301291 _86426 p q)). Qed.
Lemma lem3301294 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term850 _86426 r p q) = (term846 _86426 r p q).
Proof. exact (MK_COMB (@lem3301289 _86426 q p r) (@lem3301293 _86426 p q)). Qed.
Lemma lem3301295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301296 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term859 _86426 r p q) = (term860 _86426 r p q).
Proof. exact (MK_COMB (@lem3301295) (@lem3301294 _86426 r p q)). Qed.
Lemma lem3301297 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term852 _86426 q p r x) = (term382 _86426 q p r x).
Proof. exact (eq_refl (term852 _86426 q p r x)). Qed.
Lemma lem3301298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301299 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term861 _86426 q p r x) = (term862 _86426 q p r x).
Proof. exact (MK_COMB (@lem3301298) (@lem3301297 _86426 q p r x)). Qed.
Lemma lem3301300 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term856 _86426 p q x) = (term422 _86426 p q x).
Proof. exact (eq_refl (term856 _86426 p q x)). Qed.
Lemma lem3301301 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term863 _86426 r p q x) = (term864 _86426 r p q x).
Proof. exact (MK_COMB (@lem3301299 _86426 q p r x) (@lem3301300 _86426 p q x)). Qed.
Lemma lem3301302 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term865 _86426 r p q) = (term866 _86426 r p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301301 _86426 r p q x)). Qed.
Lemma lem3301303 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301304 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term851 _86426 r p q) = (term867 _86426 r p q).
Proof. exact (MK_COMB (@lem3301303 _86426) (@lem3301302 _86426 r p q)). Qed.
Lemma lem3301305 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term850 _86426 r p q) = (term851 _86426 r p q)) = ((term846 _86426 r p q) = (term867 _86426 r p q)).
Proof. exact (MK_COMB (@lem3301296 _86426 r p q) (@lem3301304 _86426 r p q)). Qed.
Lemma lem3301306 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term846 _86426 r p q) = (term867 _86426 r p q).
Proof. exact (EQ_MP (@lem3301305 _86426 r p q) (@lem3301283 _86426 r p q)). Qed.
Lemma lem3301307 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term848 _86426 p q) = (term868 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301306 _86426 r p q)). Qed.
Lemma lem3301308 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301309 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term849 _86426 p q) = (term869 _86426 p q).
Proof. exact (MK_COMB (@lem3301308 _86426) (@lem3301307 _86426 p q)). Qed.
Lemma lem3301310 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term827 _86426 p q) = (term869 _86426 p q).
Proof. exact (TRANS (@lem3301279 _86426 p q) (@lem3301309 _86426 p q)). Qed.
Lemma lem3301311 {_86426 : Type'} (q : _86426 -> Prop) : (term829 _86426 q) = (term870 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301310 _86426 p q)). Qed.
Lemma lem3301312 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301313 {_86426 : Type'} (q : _86426 -> Prop) : (term830 _86426 q) = (term871 _86426 q).
Proof. exact (MK_COMB (@lem3301312 _86426) (@lem3301311 _86426 q)). Qed.
Lemma lem3301314 {_86426 : Type'} (q : _86426 -> Prop) : (term809 _86426 q) = (term871 _86426 q).
Proof. exact (TRANS (@lem3301253 _86426 q) (@lem3301313 _86426 q)). Qed.
Lemma lem3301315 {_86426 : Type'} : (term811 _86426) = (term872 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301314 _86426 q)). Qed.
Lemma lem3301316 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301317 {_86426 : Type'} : (term812 _86426) = (term873 _86426).
Proof. exact (MK_COMB (@lem3301316 _86426) (@lem3301315 _86426)). Qed.
Lemma lem3301318 {_86426 : Type'} : (term446 _86426) = (term873 _86426).
Proof. exact (TRANS (@lem3301226 _86426) (@lem3301317 _86426)). Qed.
Lemma lem3301319 {_86426 : Type'} : (term764 _86426) = (term873 _86426).
Proof. exact (TRANS (@lem3301199 _86426) (@lem3301318 _86426)). Qed.
Lemma lem3301320 {_86426 : Type'} : (term765 _86426) = (term874 _86426).
Proof. exact (MK_COMB (@lem3300987 _86426) (@lem3301319 _86426)). Qed.
Lemma lem3301322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301323 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301322 (_86426 -> Prop) P Q). Qed.
Lemma lem3301324 {_86426 : Type'} : (term875 _86426) = (term876 _86426).
Proof. exact (@lem3301323 _86426 (term370 _86426) (term872 _86426)). Qed.
Lemma lem3301325 {_86426 : Type'} (q : _86426 -> Prop) : (term877 _86426 q) = (term365 _86426 q).
Proof. exact (eq_refl (term877 _86426 q)). Qed.
Lemma lem3301326 {_86426 : Type'} : (term878 _86426) = (term370 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301325 _86426 q)). Qed.
Lemma lem3301327 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301328 {_86426 : Type'} : (term879 _86426) = (term371 _86426).
Proof. exact (MK_COMB (@lem3301327 _86426) (@lem3301326 _86426)). Qed.
Lemma lem3301329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301330 {_86426 : Type'} : (term880 _86426) = (term449 _86426).
Proof. exact (MK_COMB (@lem3301329) (@lem3301328 _86426)). Qed.
Lemma lem3301331 {_86426 : Type'} (q : _86426 -> Prop) : (term881 _86426 q) = (term871 _86426 q).
Proof. exact (eq_refl (term881 _86426 q)). Qed.
Lemma lem3301332 {_86426 : Type'} : (term882 _86426) = (term872 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301331 _86426 q)). Qed.
Lemma lem3301333 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301334 {_86426 : Type'} : (term883 _86426) = (term873 _86426).
Proof. exact (MK_COMB (@lem3301333 _86426) (@lem3301332 _86426)). Qed.
Lemma lem3301335 {_86426 : Type'} : (term875 _86426) = (term874 _86426).
Proof. exact (MK_COMB (@lem3301330 _86426) (@lem3301334 _86426)). Qed.
Lemma lem3301336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301337 {_86426 : Type'} : (term884 _86426) = (term885 _86426).
Proof. exact (MK_COMB (@lem3301336) (@lem3301335 _86426)). Qed.
Lemma lem3301338 {_86426 : Type'} (q : _86426 -> Prop) : (term877 _86426 q) = (term365 _86426 q).
Proof. exact (eq_refl (term877 _86426 q)). Qed.
Lemma lem3301339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301340 {_86426 : Type'} (q : _86426 -> Prop) : (term886 _86426 q) = (term887 _86426 q).
Proof. exact (MK_COMB (@lem3301339) (@lem3301338 _86426 q)). Qed.
Lemma lem3301341 {_86426 : Type'} (q : _86426 -> Prop) : (term881 _86426 q) = (term871 _86426 q).
Proof. exact (eq_refl (term881 _86426 q)). Qed.
Lemma lem3301342 {_86426 : Type'} (q : _86426 -> Prop) : (term888 _86426 q) = (term889 _86426 q).
Proof. exact (MK_COMB (@lem3301340 _86426 q) (@lem3301341 _86426 q)). Qed.
Lemma lem3301343 {_86426 : Type'} : (term890 _86426) = (term891 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301342 _86426 q)). Qed.
Lemma lem3301344 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301345 {_86426 : Type'} : (term876 _86426) = (term892 _86426).
Proof. exact (MK_COMB (@lem3301344 _86426) (@lem3301343 _86426)). Qed.
Lemma lem3301346 {_86426 : Type'} : ((term875 _86426) = (term876 _86426)) = ((term874 _86426) = (term892 _86426)).
Proof. exact (MK_COMB (@lem3301337 _86426) (@lem3301345 _86426)). Qed.
Lemma lem3301347 {_86426 : Type'} : (term874 _86426) = (term892 _86426).
Proof. exact (EQ_MP (@lem3301346 _86426) (@lem3301324 _86426)). Qed.
Lemma lem3301349 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301350 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301349 (_86426 -> Prop) P Q). Qed.
Lemma lem3301351 {_86426 : Type'} (q : _86426 -> Prop) : (term893 _86426 q) = (term894 _86426 q).
Proof. exact (@lem3301350 _86426 (term364 _86426 q) (term870 _86426 q)). Qed.
Lemma lem3301352 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term895 _86426 q p) = (term359 _86426 p q).
Proof. exact (eq_refl (term895 _86426 q p)). Qed.
Lemma lem3301353 {_86426 : Type'} (q : _86426 -> Prop) : (term896 _86426 q) = (term364 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301352 _86426 p q)). Qed.
Lemma lem3301354 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301355 {_86426 : Type'} (q : _86426 -> Prop) : (term897 _86426 q) = (term365 _86426 q).
Proof. exact (MK_COMB (@lem3301354 _86426) (@lem3301353 _86426 q)). Qed.
Lemma lem3301356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301357 {_86426 : Type'} (q : _86426 -> Prop) : (term898 _86426 q) = (term887 _86426 q).
Proof. exact (MK_COMB (@lem3301356) (@lem3301355 _86426 q)). Qed.
Lemma lem3301358 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term899 _86426 q p) = (term869 _86426 p q).
Proof. exact (eq_refl (term899 _86426 q p)). Qed.
Lemma lem3301359 {_86426 : Type'} (q : _86426 -> Prop) : (term900 _86426 q) = (term870 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301358 _86426 p q)). Qed.
Lemma lem3301360 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301361 {_86426 : Type'} (q : _86426 -> Prop) : (term901 _86426 q) = (term871 _86426 q).
Proof. exact (MK_COMB (@lem3301360 _86426) (@lem3301359 _86426 q)). Qed.
Lemma lem3301362 {_86426 : Type'} (q : _86426 -> Prop) : (term893 _86426 q) = (term889 _86426 q).
Proof. exact (MK_COMB (@lem3301357 _86426 q) (@lem3301361 _86426 q)). Qed.
Lemma lem3301363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301364 {_86426 : Type'} (q : _86426 -> Prop) : (term902 _86426 q) = (term903 _86426 q).
Proof. exact (MK_COMB (@lem3301363) (@lem3301362 _86426 q)). Qed.
Lemma lem3301365 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term895 _86426 q p) = (term359 _86426 p q).
Proof. exact (eq_refl (term895 _86426 q p)). Qed.
Lemma lem3301366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301367 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term904 _86426 q p) = (term905 _86426 p q).
Proof. exact (MK_COMB (@lem3301366) (@lem3301365 _86426 p q)). Qed.
Lemma lem3301368 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term899 _86426 q p) = (term869 _86426 p q).
Proof. exact (eq_refl (term899 _86426 q p)). Qed.
Lemma lem3301369 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term906 _86426 q p) = (term907 _86426 p q).
Proof. exact (MK_COMB (@lem3301367 _86426 p q) (@lem3301368 _86426 p q)). Qed.
Lemma lem3301370 {_86426 : Type'} (q : _86426 -> Prop) : (term908 _86426 q) = (term909 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301369 _86426 p q)). Qed.
Lemma lem3301371 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301372 {_86426 : Type'} (q : _86426 -> Prop) : (term894 _86426 q) = (term910 _86426 q).
Proof. exact (MK_COMB (@lem3301371 _86426) (@lem3301370 _86426 q)). Qed.
Lemma lem3301373 {_86426 : Type'} (q : _86426 -> Prop) : ((term893 _86426 q) = (term894 _86426 q)) = ((term889 _86426 q) = (term910 _86426 q)).
Proof. exact (MK_COMB (@lem3301364 _86426 q) (@lem3301372 _86426 q)). Qed.
Lemma lem3301374 {_86426 : Type'} (q : _86426 -> Prop) : (term889 _86426 q) = (term910 _86426 q).
Proof. exact (EQ_MP (@lem3301373 _86426 q) (@lem3301351 _86426 q)). Qed.
Lemma lem3301376 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301377 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301376 (_86426 -> Prop) P Q). Qed.
Lemma lem3301378 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term911 _86426 p q) = (term912 _86426 p q).
Proof. exact (@lem3301377 _86426 (term358 _86426 p q) (term868 _86426 p q)). Qed.
Lemma lem3301379 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term913 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (eq_refl (term913 _86426 p q r)). Qed.
Lemma lem3301380 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term914 _86426 p q) = (term358 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301379 _86426 p q r)). Qed.
Lemma lem3301381 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301382 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term915 _86426 p q) = (term359 _86426 p q).
Proof. exact (MK_COMB (@lem3301381 _86426) (@lem3301380 _86426 p q)). Qed.
Lemma lem3301383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301384 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term916 _86426 p q) = (term905 _86426 p q).
Proof. exact (MK_COMB (@lem3301383) (@lem3301382 _86426 p q)). Qed.
Lemma lem3301385 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term917 _86426 p q r) = (term867 _86426 r p q).
Proof. exact (eq_refl (term917 _86426 p q r)). Qed.
Lemma lem3301386 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term918 _86426 p q) = (term868 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301385 _86426 r p q)). Qed.
Lemma lem3301387 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301388 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term919 _86426 p q) = (term869 _86426 p q).
Proof. exact (MK_COMB (@lem3301387 _86426) (@lem3301386 _86426 p q)). Qed.
Lemma lem3301389 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term911 _86426 p q) = (term907 _86426 p q).
Proof. exact (MK_COMB (@lem3301384 _86426 p q) (@lem3301388 _86426 p q)). Qed.
Lemma lem3301390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301391 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term920 _86426 p q) = (term921 _86426 p q).
Proof. exact (MK_COMB (@lem3301390) (@lem3301389 _86426 p q)). Qed.
Lemma lem3301392 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term913 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (eq_refl (term913 _86426 p q r)). Qed.
Lemma lem3301393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301394 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term922 _86426 p q r) = (term923 _86426 p q r).
Proof. exact (MK_COMB (@lem3301393) (@lem3301392 _86426 p q r)). Qed.
Lemma lem3301395 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term917 _86426 p q r) = (term867 _86426 r p q).
Proof. exact (eq_refl (term917 _86426 p q r)). Qed.
Lemma lem3301396 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term924 _86426 p q r) = (term925 _86426 r p q).
Proof. exact (MK_COMB (@lem3301394 _86426 p q r) (@lem3301395 _86426 r p q)). Qed.
Lemma lem3301397 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term926 _86426 p q) = (term927 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301396 _86426 r p q)). Qed.
Lemma lem3301398 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301399 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term912 _86426 p q) = (term928 _86426 p q).
Proof. exact (MK_COMB (@lem3301398 _86426) (@lem3301397 _86426 p q)). Qed.
Lemma lem3301400 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term911 _86426 p q) = (term912 _86426 p q)) = ((term907 _86426 p q) = (term928 _86426 p q)).
Proof. exact (MK_COMB (@lem3301391 _86426 p q) (@lem3301399 _86426 p q)). Qed.
Lemma lem3301401 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term907 _86426 p q) = (term928 _86426 p q).
Proof. exact (EQ_MP (@lem3301400 _86426 p q) (@lem3301378 _86426 p q)). Qed.
Lemma lem3301403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301404 {_86426 : Type'} (P : _86426 -> Prop) (Q : _86426 -> Prop) : (term458 _86426 P Q) = (term457 _86426 P Q).
Proof. exact (@lem3301403 _86426 P Q). Qed.
Lemma lem3301405 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term929 _86426 r p q) = (term930 _86426 r p q).
Proof. exact (@lem3301404 _86426 (term352 _86426 p q r) (term866 _86426 r p q)). Qed.
Lemma lem3301406 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term931 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (eq_refl (term931 _86426 p q r x)). Qed.
Lemma lem3301407 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term932 _86426 p q r) = (term352 _86426 p q r).
Proof. exact (fun_ext (fun x : _86426 => @lem3301406 _86426 p q r x)). Qed.
Lemma lem3301408 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301409 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term933 _86426 p q r) = (term353 _86426 p q r).
Proof. exact (MK_COMB (@lem3301408 _86426) (@lem3301407 _86426 p q r)). Qed.
Lemma lem3301410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301411 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : (term934 _86426 p q r) = (term923 _86426 p q r).
Proof. exact (MK_COMB (@lem3301410) (@lem3301409 _86426 p q r)). Qed.
Lemma lem3301412 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term935 _86426 r p q x) = (term864 _86426 r p q x).
Proof. exact (eq_refl (term935 _86426 r p q x)). Qed.
Lemma lem3301413 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term936 _86426 r p q) = (term866 _86426 r p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301412 _86426 r p q x)). Qed.
Lemma lem3301414 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301415 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term937 _86426 r p q) = (term867 _86426 r p q).
Proof. exact (MK_COMB (@lem3301414 _86426) (@lem3301413 _86426 r p q)). Qed.
Lemma lem3301416 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term929 _86426 r p q) = (term925 _86426 r p q).
Proof. exact (MK_COMB (@lem3301411 _86426 p q r) (@lem3301415 _86426 r p q)). Qed.
Lemma lem3301417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301418 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term938 _86426 r p q) = (term939 _86426 r p q).
Proof. exact (MK_COMB (@lem3301417) (@lem3301416 _86426 r p q)). Qed.
Lemma lem3301419 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term931 _86426 p q r x) = (term345 _86426 p q r x).
Proof. exact (eq_refl (term931 _86426 p q r x)). Qed.
Lemma lem3301420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301421 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x : _86426) : (term940 _86426 p q r x) = (term941 _86426 p q r x).
Proof. exact (MK_COMB (@lem3301420) (@lem3301419 _86426 p q r x)). Qed.
Lemma lem3301422 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term935 _86426 r p q x) = (term864 _86426 r p q x).
Proof. exact (eq_refl (term935 _86426 r p q x)). Qed.
Lemma lem3301423 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term942 _86426 r p q x) = (term943 _86426 r p q x).
Proof. exact (MK_COMB (@lem3301421 _86426 p q r x) (@lem3301422 _86426 r p q x)). Qed.
Lemma lem3301424 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term944 _86426 r p q) = (term945 _86426 r p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301423 _86426 r p q x)). Qed.
Lemma lem3301425 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301426 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term930 _86426 r p q) = (term946 _86426 r p q).
Proof. exact (MK_COMB (@lem3301425 _86426) (@lem3301424 _86426 r p q)). Qed.
Lemma lem3301427 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term929 _86426 r p q) = (term930 _86426 r p q)) = ((term925 _86426 r p q) = (term946 _86426 r p q)).
Proof. exact (MK_COMB (@lem3301418 _86426 r p q) (@lem3301426 _86426 r p q)). Qed.
Lemma lem3301428 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term925 _86426 r p q) = (term946 _86426 r p q).
Proof. exact (EQ_MP (@lem3301427 _86426 r p q) (@lem3301405 _86426 r p q)). Qed.
Lemma lem3301429 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term927 _86426 p q) = (term947 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301428 _86426 r p q)). Qed.
Lemma lem3301430 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301431 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term928 _86426 p q) = (term948 _86426 p q).
Proof. exact (MK_COMB (@lem3301430 _86426) (@lem3301429 _86426 p q)). Qed.
Lemma lem3301432 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term907 _86426 p q) = (term948 _86426 p q).
Proof. exact (TRANS (@lem3301401 _86426 p q) (@lem3301431 _86426 p q)). Qed.
Lemma lem3301433 {_86426 : Type'} (q : _86426 -> Prop) : (term909 _86426 q) = (term949 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301432 _86426 p q)). Qed.
Lemma lem3301434 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301435 {_86426 : Type'} (q : _86426 -> Prop) : (term910 _86426 q) = (term950 _86426 q).
Proof. exact (MK_COMB (@lem3301434 _86426) (@lem3301433 _86426 q)). Qed.
Lemma lem3301436 {_86426 : Type'} (q : _86426 -> Prop) : (term889 _86426 q) = (term950 _86426 q).
Proof. exact (TRANS (@lem3301374 _86426 q) (@lem3301435 _86426 q)). Qed.
Lemma lem3301437 {_86426 : Type'} : (term891 _86426) = (term951 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301436 _86426 q)). Qed.
Lemma lem3301438 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301439 {_86426 : Type'} : (term892 _86426) = (term952 _86426).
Proof. exact (MK_COMB (@lem3301438 _86426) (@lem3301437 _86426)). Qed.
Lemma lem3301440 {_86426 : Type'} : (term874 _86426) = (term952 _86426).
Proof. exact (TRANS (@lem3301347 _86426) (@lem3301439 _86426)). Qed.
Lemma lem3301441 {_86426 : Type'} : (term765 _86426) = (term952 _86426).
Proof. exact (TRANS (@lem3301320 _86426) (@lem3301440 _86426)). Qed.
Lemma lem3301442 {_86426 : Type'} : (term766 _86426) = (term953 _86426).
Proof. exact (MK_COMB (@lem3300865 _86426) (@lem3301441 _86426)). Qed.
Lemma lem3301444 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301445 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301444 (_86426 -> Prop) P Q). Qed.
Lemma lem3301446 {_86426 : Type'} : (term954 _86426) = (term955 _86426).
Proof. exact (@lem3301445 _86426 (term325 _86426) (term951 _86426)). Qed.
Lemma lem3301447 {_86426 : Type'} (q : _86426 -> Prop) : (term956 _86426 q) = (term320 _86426 q).
Proof. exact (eq_refl (term956 _86426 q)). Qed.
Lemma lem3301448 {_86426 : Type'} : (term957 _86426) = (term325 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301447 _86426 q)). Qed.
Lemma lem3301449 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301450 {_86426 : Type'} : (term958 _86426) = (term326 _86426).
Proof. exact (MK_COMB (@lem3301449 _86426) (@lem3301448 _86426)). Qed.
Lemma lem3301451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301452 {_86426 : Type'} : (term959 _86426) = (term454 _86426).
Proof. exact (MK_COMB (@lem3301451) (@lem3301450 _86426)). Qed.
Lemma lem3301453 {_86426 : Type'} (q : _86426 -> Prop) : (term960 _86426 q) = (term950 _86426 q).
Proof. exact (eq_refl (term960 _86426 q)). Qed.
Lemma lem3301454 {_86426 : Type'} : (term961 _86426) = (term951 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301453 _86426 q)). Qed.
Lemma lem3301455 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301456 {_86426 : Type'} : (term962 _86426) = (term952 _86426).
Proof. exact (MK_COMB (@lem3301455 _86426) (@lem3301454 _86426)). Qed.
Lemma lem3301457 {_86426 : Type'} : (term954 _86426) = (term953 _86426).
Proof. exact (MK_COMB (@lem3301452 _86426) (@lem3301456 _86426)). Qed.
Lemma lem3301458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301459 {_86426 : Type'} : (term963 _86426) = (term964 _86426).
Proof. exact (MK_COMB (@lem3301458) (@lem3301457 _86426)). Qed.
Lemma lem3301460 {_86426 : Type'} (q : _86426 -> Prop) : (term956 _86426 q) = (term320 _86426 q).
Proof. exact (eq_refl (term956 _86426 q)). Qed.
Lemma lem3301461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301462 {_86426 : Type'} (q : _86426 -> Prop) : (term965 _86426 q) = (term966 _86426 q).
Proof. exact (MK_COMB (@lem3301461) (@lem3301460 _86426 q)). Qed.
Lemma lem3301463 {_86426 : Type'} (q : _86426 -> Prop) : (term960 _86426 q) = (term950 _86426 q).
Proof. exact (eq_refl (term960 _86426 q)). Qed.
Lemma lem3301464 {_86426 : Type'} (q : _86426 -> Prop) : (term967 _86426 q) = (term968 _86426 q).
Proof. exact (MK_COMB (@lem3301462 _86426 q) (@lem3301463 _86426 q)). Qed.
Lemma lem3301465 {_86426 : Type'} : (term969 _86426) = (term970 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301464 _86426 q)). Qed.
Lemma lem3301466 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301467 {_86426 : Type'} : (term955 _86426) = (term971 _86426).
Proof. exact (MK_COMB (@lem3301466 _86426) (@lem3301465 _86426)). Qed.
Lemma lem3301468 {_86426 : Type'} : ((term954 _86426) = (term955 _86426)) = ((term953 _86426) = (term971 _86426)).
Proof. exact (MK_COMB (@lem3301459 _86426) (@lem3301467 _86426)). Qed.
Lemma lem3301469 {_86426 : Type'} : (term953 _86426) = (term971 _86426).
Proof. exact (EQ_MP (@lem3301468 _86426) (@lem3301446 _86426)). Qed.
Lemma lem3301471 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3301472 {_86426 : Type'} (P : type686 _86426) (Q : type686 _86426) : (term482 _86426 P Q) = (term481 _86426 P Q).
Proof. exact (@lem3301471 (_86426 -> Prop) P Q). Qed.
Lemma lem3301473 {_86426 : Type'} (q : _86426 -> Prop) : (term972 _86426 q) = (term973 _86426 q).
Proof. exact (@lem3301472 _86426 (term319 _86426 q) (term949 _86426 q)). Qed.
Lemma lem3301474 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term974 _86426 q p) = (term312 _86426 q p).
Proof. exact (eq_refl (term974 _86426 q p)). Qed.
Lemma lem3301475 {_86426 : Type'} (q : _86426 -> Prop) : (term975 _86426 q) = (term319 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301474 _86426 q p)). Qed.
Lemma lem3301476 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301477 {_86426 : Type'} (q : _86426 -> Prop) : (term976 _86426 q) = (term320 _86426 q).
Proof. exact (MK_COMB (@lem3301476 _86426) (@lem3301475 _86426 q)). Qed.
Lemma lem3301478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301479 {_86426 : Type'} (q : _86426 -> Prop) : (term977 _86426 q) = (term966 _86426 q).
Proof. exact (MK_COMB (@lem3301478) (@lem3301477 _86426 q)). Qed.
Lemma lem3301480 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term978 _86426 q p) = (term948 _86426 p q).
Proof. exact (eq_refl (term978 _86426 q p)). Qed.
Lemma lem3301481 {_86426 : Type'} (q : _86426 -> Prop) : (term979 _86426 q) = (term949 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301480 _86426 p q)). Qed.
Lemma lem3301482 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301483 {_86426 : Type'} (q : _86426 -> Prop) : (term980 _86426 q) = (term950 _86426 q).
Proof. exact (MK_COMB (@lem3301482 _86426) (@lem3301481 _86426 q)). Qed.
Lemma lem3301484 {_86426 : Type'} (q : _86426 -> Prop) : (term972 _86426 q) = (term968 _86426 q).
Proof. exact (MK_COMB (@lem3301479 _86426 q) (@lem3301483 _86426 q)). Qed.
Lemma lem3301485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301486 {_86426 : Type'} (q : _86426 -> Prop) : (term981 _86426 q) = (term982 _86426 q).
Proof. exact (MK_COMB (@lem3301485) (@lem3301484 _86426 q)). Qed.
Lemma lem3301487 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term974 _86426 q p) = (term312 _86426 q p).
Proof. exact (eq_refl (term974 _86426 q p)). Qed.
Lemma lem3301488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301489 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term983 _86426 q p) = (term984 _86426 q p).
Proof. exact (MK_COMB (@lem3301488) (@lem3301487 _86426 q p)). Qed.
Lemma lem3301490 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term978 _86426 q p) = (term948 _86426 p q).
Proof. exact (eq_refl (term978 _86426 q p)). Qed.
Lemma lem3301491 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term985 _86426 q p) = (term986 _86426 p q).
Proof. exact (MK_COMB (@lem3301489 _86426 q p) (@lem3301490 _86426 p q)). Qed.
Lemma lem3301492 {_86426 : Type'} (q : _86426 -> Prop) : (term987 _86426 q) = (term988 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301491 _86426 p q)). Qed.
Lemma lem3301493 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301494 {_86426 : Type'} (q : _86426 -> Prop) : (term973 _86426 q) = (term989 _86426 q).
Proof. exact (MK_COMB (@lem3301493 _86426) (@lem3301492 _86426 q)). Qed.
Lemma lem3301495 {_86426 : Type'} (q : _86426 -> Prop) : ((term972 _86426 q) = (term973 _86426 q)) = ((term968 _86426 q) = (term989 _86426 q)).
Proof. exact (MK_COMB (@lem3301486 _86426 q) (@lem3301494 _86426 q)). Qed.
Lemma lem3301496 {_86426 : Type'} (q : _86426 -> Prop) : (term968 _86426 q) = (term989 _86426 q).
Proof. exact (EQ_MP (@lem3301495 _86426 q) (@lem3301473 _86426 q)). Qed.
Lemma lem3301500 {A : Type'} (P : A -> Prop) (Q : Prop) : (term831 A P Q) = (term832 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3301501 {_86426 : Type'} (P : _86426 -> Prop) (Q : Prop) : (term831 _86426 P Q) = (term832 _86426 P Q).
Proof. exact (@lem3301500 _86426 P Q). Qed.
Lemma lem3301502 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term990 _86426 p q) = (term991 _86426 p q).
Proof. exact (@lem3301501 _86426 (term311 _86426 q p) (term948 _86426 p q)). Qed.
Lemma lem3301503 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term992 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (eq_refl (term992 _86426 q p x)). Qed.
Lemma lem3301504 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term993 _86426 q p) = (term311 _86426 q p).
Proof. exact (fun_ext (fun x : _86426 => @lem3301503 _86426 q p x)). Qed.
Lemma lem3301505 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301506 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term994 _86426 q p) = (term312 _86426 q p).
Proof. exact (MK_COMB (@lem3301505 _86426) (@lem3301504 _86426 q p)). Qed.
Lemma lem3301507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301508 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : (term995 _86426 q p) = (term984 _86426 q p).
Proof. exact (MK_COMB (@lem3301507) (@lem3301506 _86426 q p)). Qed.
Lemma lem3301509 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term948 _86426 p q) = (term948 _86426 p q).
Proof. exact (eq_refl (term948 _86426 p q)). Qed.
Lemma lem3301510 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term990 _86426 p q) = (term986 _86426 p q).
Proof. exact (MK_COMB (@lem3301508 _86426 q p) (@lem3301509 _86426 p q)). Qed.
Lemma lem3301511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301512 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term996 _86426 p q) = (term997 _86426 p q).
Proof. exact (MK_COMB (@lem3301511) (@lem3301510 _86426 p q)). Qed.
Lemma lem3301513 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term992 _86426 q p x) = (term302 _86426 q p x).
Proof. exact (eq_refl (term992 _86426 q p x)). Qed.
Lemma lem3301514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3301515 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term998 _86426 q p x) = (term999 _86426 q p x).
Proof. exact (MK_COMB (@lem3301514) (@lem3301513 _86426 q p x)). Qed.
Lemma lem3301516 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term948 _86426 p q) = (term948 _86426 p q).
Proof. exact (eq_refl (term948 _86426 p q)). Qed.
Lemma lem3301517 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1000 _86426 x p q) = (term1001 _86426 x p q).
Proof. exact (MK_COMB (@lem3301515 _86426 q p x) (@lem3301516 _86426 p q)). Qed.
Lemma lem3301518 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1002 _86426 p q) = (term1003 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301517 _86426 x p q)). Qed.
Lemma lem3301519 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301520 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term991 _86426 p q) = (term1004 _86426 p q).
Proof. exact (MK_COMB (@lem3301519 _86426) (@lem3301518 _86426 p q)). Qed.
Lemma lem3301521 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term990 _86426 p q) = (term991 _86426 p q)) = ((term986 _86426 p q) = (term1004 _86426 p q)).
Proof. exact (MK_COMB (@lem3301512 _86426 p q) (@lem3301520 _86426 p q)). Qed.
Lemma lem3301522 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term986 _86426 p q) = (term1004 _86426 p q).
Proof. exact (EQ_MP (@lem3301521 _86426 p q) (@lem3301502 _86426 p q)). Qed.
Lemma lem3301524 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1005 A P Q) = (term1006 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3301525 {_86426 : Type'} (P : Prop) (Q : type686 _86426) : (term1007 _86426 P Q) = (term1008 _86426 P Q).
Proof. exact (@lem3301524 (_86426 -> Prop) P Q). Qed.
Lemma lem3301526 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1009 _86426 x p q) = (term1010 _86426 x p q).
Proof. exact (@lem3301525 _86426 (term302 _86426 q p x) (term947 _86426 p q)). Qed.
Lemma lem3301527 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1011 _86426 p q r) = (term946 _86426 r p q).
Proof. exact (eq_refl (term1011 _86426 p q r)). Qed.
Lemma lem3301528 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1012 _86426 p q) = (term947 _86426 p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301527 _86426 r p q)). Qed.
Lemma lem3301529 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301530 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1013 _86426 p q) = (term948 _86426 p q).
Proof. exact (MK_COMB (@lem3301529 _86426) (@lem3301528 _86426 p q)). Qed.
Lemma lem3301531 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term999 _86426 q p x) = (term999 _86426 q p x).
Proof. exact (eq_refl (term999 _86426 q p x)). Qed.
Lemma lem3301532 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1009 _86426 x p q) = (term1001 _86426 x p q).
Proof. exact (MK_COMB (@lem3301531 _86426 q p x) (@lem3301530 _86426 p q)). Qed.
Lemma lem3301533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301534 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1014 _86426 x p q) = (term1015 _86426 x p q).
Proof. exact (MK_COMB (@lem3301533) (@lem3301532 _86426 x p q)). Qed.
Lemma lem3301535 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1011 _86426 p q r) = (term946 _86426 r p q).
Proof. exact (eq_refl (term1011 _86426 p q r)). Qed.
Lemma lem3301536 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term999 _86426 q p x) = (term999 _86426 q p x).
Proof. exact (eq_refl (term999 _86426 q p x)). Qed.
Lemma lem3301537 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1016 _86426 x p q r) = (term1017 _86426 x r p q).
Proof. exact (MK_COMB (@lem3301536 _86426 q p x) (@lem3301535 _86426 r p q)). Qed.
Lemma lem3301538 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1018 _86426 x p q) = (term1019 _86426 x p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301537 _86426 x r p q)). Qed.
Lemma lem3301539 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301540 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1010 _86426 x p q) = (term1020 _86426 x p q).
Proof. exact (MK_COMB (@lem3301539 _86426) (@lem3301538 _86426 x p q)). Qed.
Lemma lem3301541 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term1009 _86426 x p q) = (term1010 _86426 x p q)) = ((term1001 _86426 x p q) = (term1020 _86426 x p q)).
Proof. exact (MK_COMB (@lem3301534 _86426 x p q) (@lem3301540 _86426 x p q)). Qed.
Lemma lem3301542 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1001 _86426 x p q) = (term1020 _86426 x p q).
Proof. exact (EQ_MP (@lem3301541 _86426 x p q) (@lem3301526 _86426 x p q)). Qed.
Lemma lem3301544 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1005 A P Q) = (term1006 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3301545 {_86426 : Type'} (P : Prop) (Q : _86426 -> Prop) : (term1005 _86426 P Q) = (term1006 _86426 P Q).
Proof. exact (@lem3301544 _86426 P Q). Qed.
Lemma lem3301546 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1021 _86426 x r p q) = (term1022 _86426 x r p q).
Proof. exact (@lem3301545 _86426 (term302 _86426 q p x) (term945 _86426 r p q)). Qed.
Lemma lem3301547 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x : _86426) : (term1023 _86426 r p q x) = (term943 _86426 r p q x).
Proof. exact (eq_refl (term1023 _86426 r p q x)). Qed.
Lemma lem3301548 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1024 _86426 r p q) = (term945 _86426 r p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301547 _86426 r p q x)). Qed.
Lemma lem3301549 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301550 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1025 _86426 r p q) = (term946 _86426 r p q).
Proof. exact (MK_COMB (@lem3301549 _86426) (@lem3301548 _86426 r p q)). Qed.
Lemma lem3301551 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term999 _86426 q p x) = (term999 _86426 q p x).
Proof. exact (eq_refl (term999 _86426 q p x)). Qed.
Lemma lem3301552 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1021 _86426 x r p q) = (term1017 _86426 x r p q).
Proof. exact (MK_COMB (@lem3301551 _86426 q p x) (@lem3301550 _86426 r p q)). Qed.
Lemma lem3301553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3301554 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1026 _86426 x r p q) = (term1027 _86426 x r p q).
Proof. exact (MK_COMB (@lem3301553) (@lem3301552 _86426 x r p q)). Qed.
Lemma lem3301555 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) : (term1023 _86426 r p q x') = (term943 _86426 r p q x').
Proof. exact (eq_refl (term1023 _86426 r p q x')). Qed.
Lemma lem3301556 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) : (term999 _86426 q p x) = (term999 _86426 q p x).
Proof. exact (eq_refl (term999 _86426 q p x)). Qed.
Lemma lem3301557 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) : (term1028 _86426 x r p q x') = (term1029 _86426 x r p q x').
Proof. exact (MK_COMB (@lem3301556 _86426 q p x) (@lem3301555 _86426 r p q x')). Qed.
Lemma lem3301558 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1030 _86426 x r p q) = (term1031 _86426 x r p q).
Proof. exact (fun_ext (fun x' : _86426 => @lem3301557 _86426 x r p q x')). Qed.
Lemma lem3301559 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301560 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1022 _86426 x r p q) = (term1032 _86426 x r p q).
Proof. exact (MK_COMB (@lem3301559 _86426) (@lem3301558 _86426 x r p q)). Qed.
Lemma lem3301561 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : ((term1021 _86426 x r p q) = (term1022 _86426 x r p q)) = ((term1017 _86426 x r p q) = (term1032 _86426 x r p q)).
Proof. exact (MK_COMB (@lem3301554 _86426 x r p q) (@lem3301560 _86426 x r p q)). Qed.
Lemma lem3301562 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1017 _86426 x r p q) = (term1032 _86426 x r p q).
Proof. exact (EQ_MP (@lem3301561 _86426 x r p q) (@lem3301546 _86426 x r p q)). Qed.
Lemma lem3301563 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1019 _86426 x p q) = (term1033 _86426 x p q).
Proof. exact (fun_ext (fun r : _86426 -> Prop => @lem3301562 _86426 x r p q)). Qed.
Lemma lem3301564 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301565 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1020 _86426 x p q) = (term1034 _86426 x p q).
Proof. exact (MK_COMB (@lem3301564 _86426) (@lem3301563 _86426 x p q)). Qed.
Lemma lem3301566 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1001 _86426 x p q) = (term1034 _86426 x p q).
Proof. exact (TRANS (@lem3301542 _86426 x p q) (@lem3301565 _86426 x p q)). Qed.
Lemma lem3301567 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1003 _86426 p q) = (term1035 _86426 p q).
Proof. exact (fun_ext (fun x : _86426 => @lem3301566 _86426 x p q)). Qed.
Lemma lem3301568 {_86426 : Type'} : (@ex _86426) = (@ex _86426).
Proof. exact (eq_refl (@ex _86426)). Qed.
Lemma lem3301569 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1004 _86426 p q) = (term1036 _86426 p q).
Proof. exact (MK_COMB (@lem3301568 _86426) (@lem3301567 _86426 p q)). Qed.
Lemma lem3301570 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term986 _86426 p q) = (term1036 _86426 p q).
Proof. exact (TRANS (@lem3301522 _86426 p q) (@lem3301569 _86426 p q)). Qed.
Lemma lem3301571 {_86426 : Type'} (q : _86426 -> Prop) : (term988 _86426 q) = (term1037 _86426 q).
Proof. exact (fun_ext (fun p : _86426 -> Prop => @lem3301570 _86426 p q)). Qed.
Lemma lem3301572 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301573 {_86426 : Type'} (q : _86426 -> Prop) : (term989 _86426 q) = (term1038 _86426 q).
Proof. exact (MK_COMB (@lem3301572 _86426) (@lem3301571 _86426 q)). Qed.
Lemma lem3301574 {_86426 : Type'} (q : _86426 -> Prop) : (term968 _86426 q) = (term1038 _86426 q).
Proof. exact (TRANS (@lem3301496 _86426 q) (@lem3301573 _86426 q)). Qed.
Lemma lem3301575 {_86426 : Type'} : (term970 _86426) = (term1039 _86426).
Proof. exact (fun_ext (fun q : _86426 -> Prop => @lem3301574 _86426 q)). Qed.
Lemma lem3301576 {_86426 : Type'} : (@ex (_86426 -> Prop)) = (@ex (_86426 -> Prop)).
Proof. exact (eq_refl (@ex (_86426 -> Prop))). Qed.
Lemma lem3301577 {_86426 : Type'} : (term971 _86426) = (term1040 _86426).
Proof. exact (MK_COMB (@lem3301576 _86426) (@lem3301575 _86426)). Qed.
Lemma lem3301578 {_86426 : Type'} : (term953 _86426) = (term1040 _86426).
Proof. exact (TRANS (@lem3301469 _86426) (@lem3301577 _86426)). Qed.
Lemma lem3301579 {_86426 : Type'} : (term766 _86426) = (term1040 _86426).
Proof. exact (TRANS (@lem3301442 _86426) (@lem3301578 _86426)). Qed.
Lemma lem3301580 {_86426 : Type'} : (term456 _86426) = (term1040 _86426).
Proof. exact (TRANS (@lem3300774 _86426) (@lem3301579 _86426)). Qed.
Lemma lem3301581 {_86426 : Type'} : (term289 _86426) = (term1040 _86426).
Proof. exact (TRANS (@lem3298819 _86426) (@lem3301580 _86426)). Qed.
Lemma lem3301582 {_86426 : Type'} (h1 : term289 _86426) : term1040 _86426.
Proof. exact (EQ_MP (@lem3301581 _86426) (@lem3298474 _86426 h1)). Qed.
Lemma lem3301583 {_86426 : Type'} (q : _86426 -> Prop) (h1 : term1038 _86426 q) : term1038 _86426 q.
Proof. exact (h1). Qed.
Lemma lem3301584 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term1036 _86426 p q) : term1036 _86426 p q.
Proof. exact (h1). Qed.
Lemma lem3301585 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term1034 _86426 x p q) : term1034 _86426 x p q.
Proof. exact (h1). Qed.
Lemma lem3301586 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term1032 _86426 x r p q) : term1032 _86426 x r p q.
Proof. exact (h1). Qed.
Lemma lem3301879 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term1029 _86426 x r p q x') : term1029 _86426 x r p q x'.
Proof. exact (h1). Qed.
Lemma lem3301880 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term302 _86426 q p x) : term302 _86426 q p x.
Proof. exact (h1). Qed.
Lemma lem3301881 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term943 _86426 r p q x') : term943 _86426 r p q x'.
Proof. exact (h1). Qed.
Lemma lem3301882 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term298 _86426 q p x.
Proof. exact (h1). Qed.
Lemma lem3301883 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term295 _86426 q p x.
Proof. exact (h1). Qed.
Lemma lem3301884 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term291 _86426 q p x.
Proof. exact (proj2 (@lem3301882 _86426 q p x h1)). Qed.
Lemma lem3301885 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term29 _86426 p q x.
Proof. exact (proj1 (@lem3301882 _86426 q p x h1)). Qed.
Lemma lem3301890 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term29 _86426 q p x.
Proof. exact (proj2 (@lem3301883 _86426 q p x h1)). Qed.
Lemma lem3301891 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term291 _86426 p q x.
Proof. exact (proj1 (@lem3301883 _86426 q p x h1)). Qed.
Lemma lem3301896 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term345 _86426 p q r x') : term345 _86426 p q r x'.
Proof. exact (h1). Qed.
Lemma lem3301897 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term864 _86426 r p q x') : term864 _86426 r p q x'.
Proof. exact (h1). Qed.
Lemma lem3301898 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term341 _86426 p q r x'.
Proof. exact (h1). Qed.
Lemma lem3301899 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term338 _86426 p q r x'.
Proof. exact (h1). Qed.
Lemma lem3301900 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term333 _86426 p q r x'.
Proof. exact (proj2 (@lem3301898 _86426 p q r x' h1)). Qed.
Lemma lem3301901 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term40 _86426 p q r x'.
Proof. exact (proj1 (@lem3301898 _86426 p q r x' h1)). Qed.
Lemma lem3301902 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term291 _86426 q r x'.
Proof. exact (proj2 (@lem3301900 _86426 p q r x' h1)). Qed.
Lemma lem3301906 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term29 _86426 p q x') : term29 _86426 p q x'.
Proof. exact (h1). Qed.
Lemma lem3301910 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term45 _86426 p q r x'.
Proof. exact (proj2 (@lem3301899 _86426 p q r x' h1)). Qed.
Lemma lem3301911 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term329 _86426 p q r x'.
Proof. exact (proj1 (@lem3301899 _86426 p q r x' h1)). Qed.
Lemma lem3301913 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term291 _86426 p q x'.
Proof. exact (proj1 (@lem3301911 _86426 p q r x' h1)). Qed.
Lemma lem3301917 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term29 _86426 q r x') : term29 _86426 q r x'.
Proof. exact (h1). Qed.
Lemma lem3301920 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term382 _86426 q p r x') : term382 _86426 q p r x'.
Proof. exact (h1). Qed.
Lemma lem3301921 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term422 _86426 p q x') : term422 _86426 p q x'.
Proof. exact (h1). Qed.
Lemma lem3301922 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term378 _86426 q p r x'.
Proof. exact (h1). Qed.
Lemma lem3301923 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term375 _86426 q p r x'.
Proof. exact (h1). Qed.
Lemma lem3301924 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term333 _86426 q p r x'.
Proof. exact (proj2 (@lem3301922 _86426 q p r x' h1)). Qed.
Lemma lem3301925 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term45 _86426 p q r x'.
Proof. exact (proj1 (@lem3301922 _86426 q p r x' h1)). Qed.
Lemma lem3301926 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term291 _86426 p r x'.
Proof. exact (proj2 (@lem3301924 _86426 q p r x' h1)). Qed.
Lemma lem3301931 {_86426 : Type'} (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term29 _86426 q r x') : term29 _86426 q r x'.
Proof. exact (h1). Qed.
Lemma lem3301934 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term45 _86426 q p r x'.
Proof. exact (proj2 (@lem3301923 _86426 q p r x' h1)). Qed.
Lemma lem3301935 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term333 _86426 p q r x'.
Proof. exact (proj1 (@lem3301923 _86426 q p r x' h1)). Qed.
Lemma lem3301936 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term291 _86426 q r x'.
Proof. exact (proj2 (@lem3301935 _86426 q p r x' h1)). Qed.
Lemma lem3301941 {_86426 : Type'} (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term29 _86426 p r x') : term29 _86426 p r x'.
Proof. exact (h1). Qed.
Lemma lem3301944 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term418 _86426 p q x'.
Proof. exact (h1). Qed.
Lemma lem3301945 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term415 _86426 p q x'.
Proof. exact (h1). Qed.
Lemma lem3301946 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term291 _86426 p q x'.
Proof. exact (proj2 (@lem3301944 _86426 p q x' h1)). Qed.
Lemma lem3301947 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term66 _86426 p q x'.
Proof. exact (proj1 (@lem3301944 _86426 p q x' h1)). Qed.
Lemma lem3301951 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term29 _86426 p q x') : term29 _86426 p q x'.
Proof. exact (h1). Qed.
Lemma lem3301954 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term29 _86426 p q x'.
Proof. exact (proj2 (@lem3301945 _86426 p q x' h1)). Qed.
Lemma lem3301955 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term410 _86426 p q x'.
Proof. exact (proj1 (@lem3301945 _86426 p q x' h1)). Qed.
Lemma lem3301956 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term291 _86426 p q x'.
Proof. exact (proj2 (@lem3301955 _86426 p q x' h1)). Qed.
Lemma lem3301973 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (h1). Qed.
Lemma lem3301985 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (h1). Qed.
Lemma lem3301997 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (h1). Qed.
Lemma lem3302009 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (h1). Qed.
Lemma lem3302025 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302041 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302057 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302073 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302089 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302105 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302121 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302137 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302153 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302169 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302185 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302201 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302213 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302225 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302237 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302253 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302269 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302273 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term327 _86426 p x.
Proof. exact (proj2 (@lem3301884 _86426 q p x h1)). Qed.
Lemma lem3302275 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (h1). Qed.
Lemma lem3302277 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term327 _86426 q x.
Proof. exact (proj1 (@lem3301884 _86426 q p x h1)). Qed.
Lemma lem3302281 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (h1). Qed.
Lemma lem3302285 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term327 _86426 q x.
Proof. exact (proj2 (@lem3301891 _86426 q p x h1)). Qed.
Lemma lem3302287 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (h1). Qed.
Lemma lem3302289 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term327 _86426 p x.
Proof. exact (proj1 (@lem3301891 _86426 q p x h1)). Qed.
Lemma lem3302293 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (h1). Qed.
Lemma lem3302295 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301900 _86426 p q r x' h1)). Qed.
Lemma lem3302301 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302305 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term327 _86426 q x'.
Proof. exact (proj1 (@lem3301902 _86426 p q r x' h1)). Qed.
Lemma lem3302309 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302315 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term327 _86426 r x'.
Proof. exact (proj2 (@lem3301902 _86426 p q r x' h1)). Qed.
Lemma lem3302317 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302321 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301913 _86426 p q r x' h1)). Qed.
Lemma lem3302325 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302331 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term327 _86426 q x'.
Proof. exact (proj2 (@lem3301913 _86426 p q r x' h1)). Qed.
Lemma lem3302333 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302335 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term327 _86426 r x'.
Proof. exact (proj2 (@lem3301911 _86426 p q r x' h1)). Qed.
Lemma lem3302341 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302345 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301926 _86426 q p r x' h1)). Qed.
Lemma lem3302349 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302351 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term327 _86426 q x'.
Proof. exact (proj1 (@lem3301924 _86426 q p r x' h1)). Qed.
Lemma lem3302357 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302363 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term327 _86426 r x'.
Proof. exact (proj2 (@lem3301926 _86426 q p r x' h1)). Qed.
Lemma lem3302365 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302369 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term327 _86426 q x'.
Proof. exact (proj1 (@lem3301936 _86426 q p r x' h1)). Qed.
Lemma lem3302373 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302375 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301935 _86426 q p r x' h1)). Qed.
Lemma lem3302381 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302387 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term327 _86426 r x'.
Proof. exact (proj2 (@lem3301936 _86426 q p r x' h1)). Qed.
Lemma lem3302389 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302391 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301946 _86426 p q x' h1)). Qed.
Lemma lem3302395 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302397 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301946 _86426 p q x' h1)). Qed.
Lemma lem3302401 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302405 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term327 _86426 q x'.
Proof. exact (proj2 (@lem3301946 _86426 p q x' h1)). Qed.
Lemma lem3302407 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302409 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term327 _86426 p x'.
Proof. exact (proj1 (@lem3301955 _86426 p q x' h1)). Qed.
Lemma lem3302415 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302421 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term327 _86426 q x'.
Proof. exact (proj2 (@lem3301956 _86426 p q x' h1)). Qed.
Lemma lem3302423 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302425 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (h1). Qed.
Lemma lem3302426 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : term1041 _86426 p x.
Proof. exact (fun h0 : term327 _86426 p x => @lem3302425 _86426 p x h1). Qed.
Lemma lem3302428 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302429 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term1041 _86426 p x) = (p x).
Proof. exact (@lem3302428 (p x)). Qed.
Lemma lem3302430 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (EQ_MP (@lem3302429 _86426 p x) (@lem3302426 _86426 p x h1)). Qed.
Lemma lem3302433 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302435 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term327 _86426 p x) = (term1043 _86426 p x).
Proof. exact (@lem3302433 (p x)). Qed.
Lemma lem3302438 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term1043 _86426 p x.
Proof. exact (EQ_MP (@lem3302435 _86426 p x) (@lem3302273 _86426 q p x h1)). Qed.
Lemma lem3302441 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : False.
Proof. exact (@lem3302438 _86426 q p x h2 (@lem3302430 _86426 p x h1)). Qed.
Lemma lem3302442 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : term1044.
Proof. exact (fun h0 : ~ False => @lem3302441 _86426 q p x h1 h2). Qed.
Lemma lem3302444 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302445 : term1044 = False.
Proof. exact (@lem3302444 False). Qed.
Lemma lem3302446 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302445) (@lem3302442 _86426 q p x h1 h2)). Qed.
Lemma lem3302448 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (h1). Qed.
Lemma lem3302449 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : term1041 _86426 q x.
Proof. exact (fun h0 : term327 _86426 q x => @lem3302448 _86426 q x h1). Qed.
Lemma lem3302451 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302452 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term1041 _86426 q x) = (q x).
Proof. exact (@lem3302451 (q x)). Qed.
Lemma lem3302453 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (EQ_MP (@lem3302452 _86426 q x) (@lem3302449 _86426 q x h1)). Qed.
Lemma lem3302456 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302458 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term327 _86426 q x) = (term1043 _86426 q x).
Proof. exact (@lem3302456 (q x)). Qed.
Lemma lem3302461 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : term1043 _86426 q x.
Proof. exact (EQ_MP (@lem3302458 _86426 q x) (@lem3302277 _86426 q p x h1)). Qed.
Lemma lem3302464 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : False.
Proof. exact (@lem3302461 _86426 q p x h2 (@lem3302453 _86426 q x h1)). Qed.
Lemma lem3302465 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : term1044.
Proof. exact (fun h0 : ~ False => @lem3302464 _86426 q p x h1 h2). Qed.
Lemma lem3302467 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302468 : term1044 = False.
Proof. exact (@lem3302467 False). Qed.
Lemma lem3302469 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302468) (@lem3302465 _86426 q p x h1 h2)). Qed.
Lemma lem3302471 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (h1). Qed.
Lemma lem3302472 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : term1041 _86426 q x.
Proof. exact (fun h0 : term327 _86426 q x => @lem3302471 _86426 q x h1). Qed.
Lemma lem3302474 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302475 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term1041 _86426 q x) = (q x).
Proof. exact (@lem3302474 (q x)). Qed.
Lemma lem3302476 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) (h1 : q x) : q x.
Proof. exact (EQ_MP (@lem3302475 _86426 q x) (@lem3302472 _86426 q x h1)). Qed.
Lemma lem3302479 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302481 {_86426 : Type'} (q : _86426 -> Prop) (x : _86426) : (term327 _86426 q x) = (term1043 _86426 q x).
Proof. exact (@lem3302479 (q x)). Qed.
Lemma lem3302484 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term1043 _86426 q x.
Proof. exact (EQ_MP (@lem3302481 _86426 q x) (@lem3302285 _86426 q p x h1)). Qed.
Lemma lem3302487 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : False.
Proof. exact (@lem3302484 _86426 q p x h2 (@lem3302476 _86426 q x h1)). Qed.
Lemma lem3302488 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : term1044.
Proof. exact (fun h0 : ~ False => @lem3302487 _86426 q p x h1 h2). Qed.
Lemma lem3302490 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302491 : term1044 = False.
Proof. exact (@lem3302490 False). Qed.
Lemma lem3302492 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302491) (@lem3302488 _86426 q p x h1 h2)). Qed.
Lemma lem3302494 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (h1). Qed.
Lemma lem3302495 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : term1041 _86426 p x.
Proof. exact (fun h0 : term327 _86426 p x => @lem3302494 _86426 p x h1). Qed.
Lemma lem3302497 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302498 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term1041 _86426 p x) = (p x).
Proof. exact (@lem3302497 (p x)). Qed.
Lemma lem3302499 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) (h1 : p x) : p x.
Proof. exact (EQ_MP (@lem3302498 _86426 p x) (@lem3302495 _86426 p x h1)). Qed.
Lemma lem3302502 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302504 {_86426 : Type'} (p : _86426 -> Prop) (x : _86426) : (term327 _86426 p x) = (term1043 _86426 p x).
Proof. exact (@lem3302502 (p x)). Qed.
Lemma lem3302507 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : term1043 _86426 p x.
Proof. exact (EQ_MP (@lem3302504 _86426 p x) (@lem3302289 _86426 q p x h1)). Qed.
Lemma lem3302510 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : False.
Proof. exact (@lem3302507 _86426 q p x h2 (@lem3302499 _86426 p x h1)). Qed.
Lemma lem3302511 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : term1044.
Proof. exact (fun h0 : ~ False => @lem3302510 _86426 q p x h1 h2). Qed.
Lemma lem3302513 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302514 : term1044 = False.
Proof. exact (@lem3302513 False). Qed.
Lemma lem3302515 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302514) (@lem3302511 _86426 q p x h1 h2)). Qed.
Lemma lem3302517 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302518 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302517 _86426 p x' h1). Qed.
Lemma lem3302520 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302521 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302520 (p x')). Qed.
Lemma lem3302522 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302521 _86426 p x') (@lem3302518 _86426 p x' h1)). Qed.
Lemma lem3302525 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302527 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302525 (p x')). Qed.
Lemma lem3302530 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302527 _86426 p x') (@lem3302295 _86426 p q r x' h1)). Qed.
Lemma lem3302533 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (@lem3302530 _86426 p q r x' h2 (@lem3302522 _86426 p x' h1)). Qed.
Lemma lem3302534 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302533 _86426 p q r x' h1 h2). Qed.
Lemma lem3302536 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302537 : term1044 = False.
Proof. exact (@lem3302536 False). Qed.
Lemma lem3302538 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302537) (@lem3302534 _86426 p q r x' h1 h2)). Qed.
Lemma lem3302540 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302541 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : term1041 _86426 q x'.
Proof. exact (fun h0 : term327 _86426 q x' => @lem3302540 _86426 q x' h1). Qed.
Lemma lem3302543 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302544 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term1041 _86426 q x') = (q x').
Proof. exact (@lem3302543 (q x')). Qed.
Lemma lem3302545 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (EQ_MP (@lem3302544 _86426 q x') (@lem3302541 _86426 q x' h1)). Qed.
Lemma lem3302548 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302550 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term327 _86426 q x') = (term1043 _86426 q x').
Proof. exact (@lem3302548 (q x')). Qed.
Lemma lem3302553 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term1043 _86426 q x'.
Proof. exact (EQ_MP (@lem3302550 _86426 q x') (@lem3302305 _86426 p q r x' h1)). Qed.
Lemma lem3302556 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (@lem3302553 _86426 p q r x' h2 (@lem3302545 _86426 q x' h1)). Qed.
Lemma lem3302557 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302556 _86426 p q r x' h1 h2). Qed.
Lemma lem3302559 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302560 : term1044 = False.
Proof. exact (@lem3302559 False). Qed.
Lemma lem3302561 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302560) (@lem3302557 _86426 p q r x' h1 h2)). Qed.
Lemma lem3302563 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302564 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : term1041 _86426 r x'.
Proof. exact (fun h0 : term327 _86426 r x' => @lem3302563 _86426 r x' h1). Qed.
Lemma lem3302566 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302567 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term1041 _86426 r x') = (r x').
Proof. exact (@lem3302566 (r x')). Qed.
Lemma lem3302568 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (EQ_MP (@lem3302567 _86426 r x') (@lem3302564 _86426 r x' h1)). Qed.
Lemma lem3302571 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302573 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term327 _86426 r x') = (term1043 _86426 r x').
Proof. exact (@lem3302571 (r x')). Qed.
Lemma lem3302576 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : term1043 _86426 r x'.
Proof. exact (EQ_MP (@lem3302573 _86426 r x') (@lem3302315 _86426 p q r x' h1)). Qed.
Lemma lem3302579 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (@lem3302576 _86426 p q r x' h2 (@lem3302568 _86426 r x' h1)). Qed.
Lemma lem3302580 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302579 _86426 p q r x' h1 h2). Qed.
Lemma lem3302582 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302583 : term1044 = False.
Proof. exact (@lem3302582 False). Qed.
Lemma lem3302584 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302583) (@lem3302580 _86426 p q r x' h1 h2)). Qed.
Lemma lem3302586 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302587 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302586 _86426 p x' h1). Qed.
Lemma lem3302589 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302590 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302589 (p x')). Qed.
Lemma lem3302591 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302590 _86426 p x') (@lem3302587 _86426 p x' h1)). Qed.
Lemma lem3302594 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302596 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302594 (p x')). Qed.
Lemma lem3302599 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302596 _86426 p x') (@lem3302321 _86426 p q r x' h1)). Qed.
Lemma lem3302602 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (@lem3302599 _86426 p q r x' h2 (@lem3302591 _86426 p x' h1)). Qed.
Lemma lem3302603 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302602 _86426 p q r x' h1 h2). Qed.
Lemma lem3302605 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302606 : term1044 = False.
Proof. exact (@lem3302605 False). Qed.
Lemma lem3302607 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302606) (@lem3302603 _86426 p q r x' h1 h2)). Qed.
Lemma lem3302609 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302610 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : term1041 _86426 q x'.
Proof. exact (fun h0 : term327 _86426 q x' => @lem3302609 _86426 q x' h1). Qed.
Lemma lem3302612 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302613 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term1041 _86426 q x') = (q x').
Proof. exact (@lem3302612 (q x')). Qed.
Lemma lem3302614 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (EQ_MP (@lem3302613 _86426 q x') (@lem3302610 _86426 q x' h1)). Qed.
Lemma lem3302617 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302619 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term327 _86426 q x') = (term1043 _86426 q x').
Proof. exact (@lem3302617 (q x')). Qed.
Lemma lem3302622 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term1043 _86426 q x'.
Proof. exact (EQ_MP (@lem3302619 _86426 q x') (@lem3302331 _86426 p q r x' h1)). Qed.
Lemma lem3302625 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (@lem3302622 _86426 p q r x' h2 (@lem3302614 _86426 q x' h1)). Qed.
Lemma lem3302626 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302625 _86426 p q r x' h1 h2). Qed.
Lemma lem3302628 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302629 : term1044 = False.
Proof. exact (@lem3302628 False). Qed.
Lemma lem3302630 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302629) (@lem3302626 _86426 p q r x' h1 h2)). Qed.
Lemma lem3302632 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302633 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : term1041 _86426 r x'.
Proof. exact (fun h0 : term327 _86426 r x' => @lem3302632 _86426 r x' h1). Qed.
Lemma lem3302635 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302636 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term1041 _86426 r x') = (r x').
Proof. exact (@lem3302635 (r x')). Qed.
Lemma lem3302637 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (EQ_MP (@lem3302636 _86426 r x') (@lem3302633 _86426 r x' h1)). Qed.
Lemma lem3302640 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302642 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term327 _86426 r x') = (term1043 _86426 r x').
Proof. exact (@lem3302640 (r x')). Qed.
Lemma lem3302645 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : term1043 _86426 r x'.
Proof. exact (EQ_MP (@lem3302642 _86426 r x') (@lem3302335 _86426 p q r x' h1)). Qed.
Lemma lem3302648 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (@lem3302645 _86426 p q r x' h2 (@lem3302637 _86426 r x' h1)). Qed.
Lemma lem3302649 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302648 _86426 p q r x' h1 h2). Qed.
Lemma lem3302651 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302652 : term1044 = False.
Proof. exact (@lem3302651 False). Qed.
Lemma lem3302653 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302652) (@lem3302649 _86426 p q r x' h1 h2)). Qed.
Lemma lem3302655 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302656 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302655 _86426 p x' h1). Qed.
Lemma lem3302658 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302659 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302658 (p x')). Qed.
Lemma lem3302660 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302659 _86426 p x') (@lem3302656 _86426 p x' h1)). Qed.
Lemma lem3302663 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302665 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302663 (p x')). Qed.
Lemma lem3302668 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302665 _86426 p x') (@lem3302345 _86426 q p r x' h1)). Qed.
Lemma lem3302671 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (@lem3302668 _86426 q p r x' h2 (@lem3302660 _86426 p x' h1)). Qed.
Lemma lem3302672 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302671 _86426 q p r x' h1 h2). Qed.
Lemma lem3302674 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302675 : term1044 = False.
Proof. exact (@lem3302674 False). Qed.
Lemma lem3302676 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302675) (@lem3302672 _86426 q p r x' h1 h2)). Qed.
Lemma lem3302678 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302679 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : term1041 _86426 q x'.
Proof. exact (fun h0 : term327 _86426 q x' => @lem3302678 _86426 q x' h1). Qed.
Lemma lem3302681 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302682 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term1041 _86426 q x') = (q x').
Proof. exact (@lem3302681 (q x')). Qed.
Lemma lem3302683 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (EQ_MP (@lem3302682 _86426 q x') (@lem3302679 _86426 q x' h1)). Qed.
Lemma lem3302686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302688 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term327 _86426 q x') = (term1043 _86426 q x').
Proof. exact (@lem3302686 (q x')). Qed.
Lemma lem3302691 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term1043 _86426 q x'.
Proof. exact (EQ_MP (@lem3302688 _86426 q x') (@lem3302351 _86426 q p r x' h1)). Qed.
Lemma lem3302694 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (@lem3302691 _86426 q p r x' h2 (@lem3302683 _86426 q x' h1)). Qed.
Lemma lem3302695 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302694 _86426 q p r x' h1 h2). Qed.
Lemma lem3302697 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302698 : term1044 = False.
Proof. exact (@lem3302697 False). Qed.
Lemma lem3302699 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302698) (@lem3302695 _86426 q p r x' h1 h2)). Qed.
Lemma lem3302701 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302702 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : term1041 _86426 r x'.
Proof. exact (fun h0 : term327 _86426 r x' => @lem3302701 _86426 r x' h1). Qed.
Lemma lem3302704 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302705 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term1041 _86426 r x') = (r x').
Proof. exact (@lem3302704 (r x')). Qed.
Lemma lem3302706 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (EQ_MP (@lem3302705 _86426 r x') (@lem3302702 _86426 r x' h1)). Qed.
Lemma lem3302709 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302711 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term327 _86426 r x') = (term1043 _86426 r x').
Proof. exact (@lem3302709 (r x')). Qed.
Lemma lem3302714 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : term1043 _86426 r x'.
Proof. exact (EQ_MP (@lem3302711 _86426 r x') (@lem3302363 _86426 q p r x' h1)). Qed.
Lemma lem3302717 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (@lem3302714 _86426 q p r x' h2 (@lem3302706 _86426 r x' h1)). Qed.
Lemma lem3302718 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302717 _86426 q p r x' h1 h2). Qed.
Lemma lem3302720 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302721 : term1044 = False.
Proof. exact (@lem3302720 False). Qed.
Lemma lem3302722 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302721) (@lem3302718 _86426 q p r x' h1 h2)). Qed.
Lemma lem3302724 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302725 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : term1041 _86426 q x'.
Proof. exact (fun h0 : term327 _86426 q x' => @lem3302724 _86426 q x' h1). Qed.
Lemma lem3302727 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302728 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term1041 _86426 q x') = (q x').
Proof. exact (@lem3302727 (q x')). Qed.
Lemma lem3302729 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (EQ_MP (@lem3302728 _86426 q x') (@lem3302725 _86426 q x' h1)). Qed.
Lemma lem3302732 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302734 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term327 _86426 q x') = (term1043 _86426 q x').
Proof. exact (@lem3302732 (q x')). Qed.
Lemma lem3302737 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term1043 _86426 q x'.
Proof. exact (EQ_MP (@lem3302734 _86426 q x') (@lem3302369 _86426 q p r x' h1)). Qed.
Lemma lem3302740 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (@lem3302737 _86426 q p r x' h2 (@lem3302729 _86426 q x' h1)). Qed.
Lemma lem3302741 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302740 _86426 q p r x' h1 h2). Qed.
Lemma lem3302743 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302744 : term1044 = False.
Proof. exact (@lem3302743 False). Qed.
Lemma lem3302745 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302744) (@lem3302741 _86426 q p r x' h1 h2)). Qed.
Lemma lem3302747 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302748 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302747 _86426 p x' h1). Qed.
Lemma lem3302750 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302751 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302750 (p x')). Qed.
Lemma lem3302752 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302751 _86426 p x') (@lem3302748 _86426 p x' h1)). Qed.
Lemma lem3302755 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302757 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302755 (p x')). Qed.
Lemma lem3302760 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302757 _86426 p x') (@lem3302375 _86426 q p r x' h1)). Qed.
Lemma lem3302763 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (@lem3302760 _86426 q p r x' h2 (@lem3302752 _86426 p x' h1)). Qed.
Lemma lem3302764 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302763 _86426 q p r x' h1 h2). Qed.
Lemma lem3302766 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302767 : term1044 = False.
Proof. exact (@lem3302766 False). Qed.
Lemma lem3302768 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302767) (@lem3302764 _86426 q p r x' h1 h2)). Qed.
Lemma lem3302770 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (h1). Qed.
Lemma lem3302771 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : term1041 _86426 r x'.
Proof. exact (fun h0 : term327 _86426 r x' => @lem3302770 _86426 r x' h1). Qed.
Lemma lem3302773 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302774 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term1041 _86426 r x') = (r x').
Proof. exact (@lem3302773 (r x')). Qed.
Lemma lem3302775 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) (h1 : r x') : r x'.
Proof. exact (EQ_MP (@lem3302774 _86426 r x') (@lem3302771 _86426 r x' h1)). Qed.
Lemma lem3302778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302780 {_86426 : Type'} (r : _86426 -> Prop) (x' : _86426) : (term327 _86426 r x') = (term1043 _86426 r x').
Proof. exact (@lem3302778 (r x')). Qed.
Lemma lem3302783 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : term1043 _86426 r x'.
Proof. exact (EQ_MP (@lem3302780 _86426 r x') (@lem3302387 _86426 q p r x' h1)). Qed.
Lemma lem3302786 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (@lem3302783 _86426 q p r x' h2 (@lem3302775 _86426 r x' h1)). Qed.
Lemma lem3302787 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302786 _86426 q p r x' h1 h2). Qed.
Lemma lem3302789 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302790 : term1044 = False.
Proof. exact (@lem3302789 False). Qed.
Lemma lem3302791 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302790) (@lem3302787 _86426 q p r x' h1 h2)). Qed.
Lemma lem3302793 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302794 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302793 _86426 p x' h1). Qed.
Lemma lem3302796 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302797 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302796 (p x')). Qed.
Lemma lem3302798 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302797 _86426 p x') (@lem3302794 _86426 p x' h1)). Qed.
Lemma lem3302801 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302803 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302801 (p x')). Qed.
Lemma lem3302806 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302803 _86426 p x') (@lem3302391 _86426 p q x' h1)). Qed.
Lemma lem3302809 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (@lem3302806 _86426 p q x' h2 (@lem3302798 _86426 p x' h1)). Qed.
Lemma lem3302810 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302809 _86426 p q x' h1 h2). Qed.
Lemma lem3302812 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302813 : term1044 = False.
Proof. exact (@lem3302812 False). Qed.
Lemma lem3302814 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302813) (@lem3302810 _86426 p q x' h1 h2)). Qed.
Lemma lem3302816 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302817 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302816 _86426 p x' h1). Qed.
Lemma lem3302819 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302820 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302819 (p x')). Qed.
Lemma lem3302821 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302820 _86426 p x') (@lem3302817 _86426 p x' h1)). Qed.
Lemma lem3302824 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302826 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302824 (p x')). Qed.
Lemma lem3302829 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302826 _86426 p x') (@lem3302397 _86426 p q x' h1)). Qed.
Lemma lem3302832 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (@lem3302829 _86426 p q x' h2 (@lem3302821 _86426 p x' h1)). Qed.
Lemma lem3302833 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302832 _86426 p q x' h1 h2). Qed.
Lemma lem3302835 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302836 : term1044 = False.
Proof. exact (@lem3302835 False). Qed.
Lemma lem3302837 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302836) (@lem3302833 _86426 p q x' h1 h2)). Qed.
Lemma lem3302839 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302840 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : term1041 _86426 q x'.
Proof. exact (fun h0 : term327 _86426 q x' => @lem3302839 _86426 q x' h1). Qed.
Lemma lem3302842 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302843 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term1041 _86426 q x') = (q x').
Proof. exact (@lem3302842 (q x')). Qed.
Lemma lem3302844 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (EQ_MP (@lem3302843 _86426 q x') (@lem3302840 _86426 q x' h1)). Qed.
Lemma lem3302847 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302849 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term327 _86426 q x') = (term1043 _86426 q x').
Proof. exact (@lem3302847 (q x')). Qed.
Lemma lem3302852 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : term1043 _86426 q x'.
Proof. exact (EQ_MP (@lem3302849 _86426 q x') (@lem3302405 _86426 p q x' h1)). Qed.
Lemma lem3302855 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : False.
Proof. exact (@lem3302852 _86426 p q x' h2 (@lem3302844 _86426 q x' h1)). Qed.
Lemma lem3302856 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302855 _86426 p q x' h1 h2). Qed.
Lemma lem3302858 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302859 : term1044 = False.
Proof. exact (@lem3302858 False). Qed.
Lemma lem3302860 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302859) (@lem3302856 _86426 p q x' h1 h2)). Qed.
Lemma lem3302862 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (h1). Qed.
Lemma lem3302863 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : term1041 _86426 p x'.
Proof. exact (fun h0 : term327 _86426 p x' => @lem3302862 _86426 p x' h1). Qed.
Lemma lem3302865 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302866 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term1041 _86426 p x') = (p x').
Proof. exact (@lem3302865 (p x')). Qed.
Lemma lem3302867 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) (h1 : p x') : p x'.
Proof. exact (EQ_MP (@lem3302866 _86426 p x') (@lem3302863 _86426 p x' h1)). Qed.
Lemma lem3302870 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302872 {_86426 : Type'} (p : _86426 -> Prop) (x' : _86426) : (term327 _86426 p x') = (term1043 _86426 p x').
Proof. exact (@lem3302870 (p x')). Qed.
Lemma lem3302875 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term1043 _86426 p x'.
Proof. exact (EQ_MP (@lem3302872 _86426 p x') (@lem3302409 _86426 p q x' h1)). Qed.
Lemma lem3302878 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : False.
Proof. exact (@lem3302875 _86426 p q x' h2 (@lem3302867 _86426 p x' h1)). Qed.
Lemma lem3302879 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302878 _86426 p q x' h1 h2). Qed.
Lemma lem3302881 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302882 : term1044 = False.
Proof. exact (@lem3302881 False). Qed.
Lemma lem3302883 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302882) (@lem3302879 _86426 p q x' h1 h2)). Qed.
Lemma lem3302885 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (h1). Qed.
Lemma lem3302886 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : term1041 _86426 q x'.
Proof. exact (fun h0 : term327 _86426 q x' => @lem3302885 _86426 q x' h1). Qed.
Lemma lem3302888 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302889 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term1041 _86426 q x') = (q x').
Proof. exact (@lem3302888 (q x')). Qed.
Lemma lem3302890 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) (h1 : q x') : q x'.
Proof. exact (EQ_MP (@lem3302889 _86426 q x') (@lem3302886 _86426 q x' h1)). Qed.
Lemma lem3302893 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3302895 {_86426 : Type'} (q : _86426 -> Prop) (x' : _86426) : (term327 _86426 q x') = (term1043 _86426 q x').
Proof. exact (@lem3302893 (q x')). Qed.
Lemma lem3302898 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : term1043 _86426 q x'.
Proof. exact (EQ_MP (@lem3302895 _86426 q x') (@lem3302421 _86426 p q x' h1)). Qed.
Lemma lem3302901 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : False.
Proof. exact (@lem3302898 _86426 p q x' h2 (@lem3302890 _86426 q x' h1)). Qed.
Lemma lem3302902 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : term1044.
Proof. exact (fun h0 : ~ False => @lem3302901 _86426 p q x' h1 h2). Qed.
Lemma lem3302904 (p : Prop) : (term1042 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3302905 : term1044 = False.
Proof. exact (@lem3302904 False). Qed.
Lemma lem3302906 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302905) (@lem3302902 _86426 p q x' h1 h2)). Qed.
Lemma lem3302907 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302906 _86426 p q x' h1 h2) (fun h3 : False => @lem3302423 _86426 q x' h1)). Qed.
Lemma lem3302908 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302907 _86426 p q x' h1 h2) (@lem3302423 _86426 q x' h1)). Qed.
Lemma lem3302909 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302883 _86426 p q x' h1 h2) (fun h3 : False => @lem3302415 _86426 p x' h1)). Qed.
Lemma lem3302910 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302909 _86426 p q x' h1 h2) (@lem3302415 _86426 p x' h1)). Qed.
Lemma lem3302911 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302860 _86426 p q x' h1 h2) (fun h3 : False => @lem3302407 _86426 q x' h1)). Qed.
Lemma lem3302912 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302911 _86426 p q x' h1 h2) (@lem3302407 _86426 q x' h1)). Qed.
Lemma lem3302913 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302837 _86426 p q x' h1 h2) (fun h3 : False => @lem3302401 _86426 p x' h1)). Qed.
Lemma lem3302914 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302913 _86426 p q x' h1 h2) (@lem3302401 _86426 p x' h1)). Qed.
Lemma lem3302915 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302814 _86426 p q x' h1 h2) (fun h3 : False => @lem3302395 _86426 p x' h1)). Qed.
Lemma lem3302916 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302915 _86426 p q x' h1 h2) (@lem3302395 _86426 p x' h1)). Qed.
Lemma lem3302917 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302791 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302389 _86426 r x' h1)). Qed.
Lemma lem3302918 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302917 _86426 q p r x' h1 h2) (@lem3302389 _86426 r x' h1)). Qed.
Lemma lem3302919 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302768 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302381 _86426 p x' h1)). Qed.
Lemma lem3302920 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302919 _86426 q p r x' h1 h2) (@lem3302381 _86426 p x' h1)). Qed.
Lemma lem3302921 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302745 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302373 _86426 q x' h1)). Qed.
Lemma lem3302922 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302921 _86426 q p r x' h1 h2) (@lem3302373 _86426 q x' h1)). Qed.
Lemma lem3302923 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302722 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302365 _86426 r x' h1)). Qed.
Lemma lem3302924 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302923 _86426 q p r x' h1 h2) (@lem3302365 _86426 r x' h1)). Qed.
Lemma lem3302925 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302699 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302357 _86426 q x' h1)). Qed.
Lemma lem3302926 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302925 _86426 q p r x' h1 h2) (@lem3302357 _86426 q x' h1)). Qed.
Lemma lem3302927 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302676 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302349 _86426 p x' h1)). Qed.
Lemma lem3302928 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302927 _86426 q p r x' h1 h2) (@lem3302349 _86426 p x' h1)). Qed.
Lemma lem3302929 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302653 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302341 _86426 r x' h1)). Qed.
Lemma lem3302930 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302929 _86426 p q r x' h1 h2) (@lem3302341 _86426 r x' h1)). Qed.
Lemma lem3302931 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302630 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302333 _86426 q x' h1)). Qed.
Lemma lem3302932 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302931 _86426 p q r x' h1 h2) (@lem3302333 _86426 q x' h1)). Qed.
Lemma lem3302933 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302607 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302325 _86426 p x' h1)). Qed.
Lemma lem3302934 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302933 _86426 p q r x' h1 h2) (@lem3302325 _86426 p x' h1)). Qed.
Lemma lem3302935 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302584 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302317 _86426 r x' h1)). Qed.
Lemma lem3302936 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302935 _86426 p q r x' h1 h2) (@lem3302317 _86426 r x' h1)). Qed.
Lemma lem3302937 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302561 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302309 _86426 q x' h1)). Qed.
Lemma lem3302938 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302937 _86426 p q r x' h1 h2) (@lem3302309 _86426 q x' h1)). Qed.
Lemma lem3302939 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302538 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302301 _86426 p x' h1)). Qed.
Lemma lem3302940 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302939 _86426 p q r x' h1 h2) (@lem3302301 _86426 p x' h1)). Qed.
Lemma lem3302941 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : (p x) = False.
Proof. exact (prop_ext (fun h3 : p x => @lem3302515 _86426 q p x h1 h2) (fun h3 : False => @lem3302293 _86426 p x h1)). Qed.
Lemma lem3302942 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302941 _86426 q p x h1 h2) (@lem3302293 _86426 p x h1)). Qed.
Lemma lem3302943 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : (q x) = False.
Proof. exact (prop_ext (fun h3 : q x => @lem3302492 _86426 q p x h1 h2) (fun h3 : False => @lem3302287 _86426 q x h1)). Qed.
Lemma lem3302944 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302943 _86426 q p x h1 h2) (@lem3302287 _86426 q x h1)). Qed.
Lemma lem3302945 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : (q x) = False.
Proof. exact (prop_ext (fun h3 : q x => @lem3302469 _86426 q p x h1 h2) (fun h3 : False => @lem3302281 _86426 q x h1)). Qed.
Lemma lem3302946 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302945 _86426 q p x h1 h2) (@lem3302281 _86426 q x h1)). Qed.
Lemma lem3302947 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : (p x) = False.
Proof. exact (prop_ext (fun h3 : p x => @lem3302446 _86426 q p x h1 h2) (fun h3 : False => @lem3302275 _86426 p x h1)). Qed.
Lemma lem3302948 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302947 _86426 q p x h1 h2) (@lem3302275 _86426 p x h1)). Qed.
Lemma lem3302949 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302908 _86426 p q x' h1 h2) (fun h3 : False => @lem3302269 _86426 q x' h1)). Qed.
Lemma lem3302950 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302949 _86426 p q x' h1 h2) (@lem3302269 _86426 q x' h1)). Qed.
Lemma lem3302951 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302910 _86426 p q x' h1 h2) (fun h3 : False => @lem3302253 _86426 p x' h1)). Qed.
Lemma lem3302952 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302951 _86426 p q x' h1 h2) (@lem3302253 _86426 p x' h1)). Qed.
Lemma lem3302953 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302912 _86426 p q x' h1 h2) (fun h3 : False => @lem3302237 _86426 q x' h1)). Qed.
Lemma lem3302954 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302953 _86426 p q x' h1 h2) (@lem3302237 _86426 q x' h1)). Qed.
Lemma lem3302955 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302914 _86426 p q x' h1 h2) (fun h3 : False => @lem3302225 _86426 p x' h1)). Qed.
Lemma lem3302956 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302955 _86426 p q x' h1 h2) (@lem3302225 _86426 p x' h1)). Qed.
Lemma lem3302957 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302916 _86426 p q x' h1 h2) (fun h3 : False => @lem3302213 _86426 p x' h1)). Qed.
Lemma lem3302958 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302957 _86426 p q x' h1 h2) (@lem3302213 _86426 p x' h1)). Qed.
Lemma lem3302959 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302918 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302201 _86426 r x' h1)). Qed.
Lemma lem3302960 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302959 _86426 q p r x' h1 h2) (@lem3302201 _86426 r x' h1)). Qed.
Lemma lem3302961 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302920 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302185 _86426 p x' h1)). Qed.
Lemma lem3302962 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302961 _86426 q p r x' h1 h2) (@lem3302185 _86426 p x' h1)). Qed.
Lemma lem3302963 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302922 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302169 _86426 q x' h1)). Qed.
Lemma lem3302964 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302963 _86426 q p r x' h1 h2) (@lem3302169 _86426 q x' h1)). Qed.
Lemma lem3302965 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302924 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302153 _86426 r x' h1)). Qed.
Lemma lem3302966 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302965 _86426 q p r x' h1 h2) (@lem3302153 _86426 r x' h1)). Qed.
Lemma lem3302967 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302926 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302137 _86426 q x' h1)). Qed.
Lemma lem3302968 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302967 _86426 q p r x' h1 h2) (@lem3302137 _86426 q x' h1)). Qed.
Lemma lem3302969 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302928 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302121 _86426 p x' h1)). Qed.
Lemma lem3302970 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3302969 _86426 q p r x' h1 h2) (@lem3302121 _86426 p x' h1)). Qed.
Lemma lem3302971 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302930 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302105 _86426 r x' h1)). Qed.
Lemma lem3302972 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302971 _86426 p q r x' h1 h2) (@lem3302105 _86426 r x' h1)). Qed.
Lemma lem3302973 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302932 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302089 _86426 q x' h1)). Qed.
Lemma lem3302974 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302973 _86426 p q r x' h1 h2) (@lem3302089 _86426 q x' h1)). Qed.
Lemma lem3302975 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302934 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302073 _86426 p x' h1)). Qed.
Lemma lem3302976 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302975 _86426 p q r x' h1 h2) (@lem3302073 _86426 p x' h1)). Qed.
Lemma lem3302977 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302936 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302057 _86426 r x' h1)). Qed.
Lemma lem3302978 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302977 _86426 p q r x' h1 h2) (@lem3302057 _86426 r x' h1)). Qed.
Lemma lem3302979 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302938 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302041 _86426 q x' h1)). Qed.
Lemma lem3302980 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302979 _86426 p q r x' h1 h2) (@lem3302041 _86426 q x' h1)). Qed.
Lemma lem3302981 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302940 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302025 _86426 p x' h1)). Qed.
Lemma lem3302982 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3302981 _86426 p q r x' h1 h2) (@lem3302025 _86426 p x' h1)). Qed.
Lemma lem3302983 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : (p x) = False.
Proof. exact (prop_ext (fun h3 : p x => @lem3302942 _86426 q p x h1 h2) (fun h3 : False => @lem3302009 _86426 p x h1)). Qed.
Lemma lem3302984 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302983 _86426 q p x h1 h2) (@lem3302009 _86426 p x h1)). Qed.
Lemma lem3302985 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : (q x) = False.
Proof. exact (prop_ext (fun h3 : q x => @lem3302944 _86426 q p x h1 h2) (fun h3 : False => @lem3301997 _86426 q x h1)). Qed.
Lemma lem3302986 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302985 _86426 q p x h1 h2) (@lem3301997 _86426 q x h1)). Qed.
Lemma lem3302987 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : (q x) = False.
Proof. exact (prop_ext (fun h3 : q x => @lem3302946 _86426 q p x h1 h2) (fun h3 : False => @lem3301985 _86426 q x h1)). Qed.
Lemma lem3302988 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302987 _86426 q p x h1 h2) (@lem3301985 _86426 q x h1)). Qed.
Lemma lem3302989 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : (p x) = False.
Proof. exact (prop_ext (fun h3 : p x => @lem3302948 _86426 q p x h1 h2) (fun h3 : False => @lem3301973 _86426 p x h1)). Qed.
Lemma lem3302990 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3302989 _86426 q p x h1 h2) (@lem3301973 _86426 p x h1)). Qed.
Lemma lem3302991 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302950 _86426 p q x' h1 h2) (fun h3 : False => @lem3302269 _86426 q x' h1)). Qed.
Lemma lem3302992 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302991 _86426 p q x' h1 h2) (@lem3302269 _86426 q x' h1)). Qed.
Lemma lem3302993 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302952 _86426 p q x' h1 h2) (fun h3 : False => @lem3302253 _86426 p x' h1)). Qed.
Lemma lem3302994 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term415 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302993 _86426 p q x' h1 h2) (@lem3302253 _86426 p x' h1)). Qed.
Lemma lem3302995 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302954 _86426 p q x' h1 h2) (fun h3 : False => @lem3302237 _86426 q x' h1)). Qed.
Lemma lem3302996 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302995 _86426 p q x' h1 h2) (@lem3302237 _86426 q x' h1)). Qed.
Lemma lem3302997 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302956 _86426 p q x' h1 h2) (fun h3 : False => @lem3302225 _86426 p x' h1)). Qed.
Lemma lem3302998 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302997 _86426 p q x' h1 h2) (@lem3302225 _86426 p x' h1)). Qed.
Lemma lem3302999 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302958 _86426 p q x' h1 h2) (fun h3 : False => @lem3302213 _86426 p x' h1)). Qed.
Lemma lem3303000 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term418 _86426 p q x') : False.
Proof. exact (EQ_MP (@lem3302999 _86426 p q x' h1 h2) (@lem3302213 _86426 p x' h1)). Qed.
Lemma lem3303001 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302960 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302201 _86426 r x' h1)). Qed.
Lemma lem3303002 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3303001 _86426 q p r x' h1 h2) (@lem3302201 _86426 r x' h1)). Qed.
Lemma lem3303003 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302962 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302185 _86426 p x' h1)). Qed.
Lemma lem3303004 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3303003 _86426 q p r x' h1 h2) (@lem3302185 _86426 p x' h1)). Qed.
Lemma lem3303005 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302964 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302169 _86426 q x' h1)). Qed.
Lemma lem3303006 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term375 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3303005 _86426 q p r x' h1 h2) (@lem3302169 _86426 q x' h1)). Qed.
Lemma lem3303007 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302966 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302153 _86426 r x' h1)). Qed.
Lemma lem3303008 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3303007 _86426 q p r x' h1 h2) (@lem3302153 _86426 r x' h1)). Qed.
Lemma lem3303009 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302968 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302137 _86426 q x' h1)). Qed.
Lemma lem3303010 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3303009 _86426 q p r x' h1 h2) (@lem3302137 _86426 q x' h1)). Qed.
Lemma lem3303011 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302970 _86426 q p r x' h1 h2) (fun h3 : False => @lem3302121 _86426 p x' h1)). Qed.
Lemma lem3303012 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term378 _86426 q p r x') : False.
Proof. exact (EQ_MP (@lem3303011 _86426 q p r x' h1 h2) (@lem3302121 _86426 p x' h1)). Qed.
Lemma lem3303013 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302972 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302105 _86426 r x' h1)). Qed.
Lemma lem3303014 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3303013 _86426 p q r x' h1 h2) (@lem3302105 _86426 r x' h1)). Qed.
Lemma lem3303015 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302974 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302089 _86426 q x' h1)). Qed.
Lemma lem3303016 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3303015 _86426 p q r x' h1 h2) (@lem3302089 _86426 q x' h1)). Qed.
Lemma lem3303017 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302976 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302073 _86426 p x' h1)). Qed.
Lemma lem3303018 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term338 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3303017 _86426 p q r x' h1 h2) (@lem3302073 _86426 p x' h1)). Qed.
Lemma lem3303019 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : (r x') = False.
Proof. exact (prop_ext (fun h3 : r x' => @lem3302978 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302057 _86426 r x' h1)). Qed.
Lemma lem3303020 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : r x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3303019 _86426 p q r x' h1 h2) (@lem3302057 _86426 r x' h1)). Qed.
Lemma lem3303021 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : (q x') = False.
Proof. exact (prop_ext (fun h3 : q x' => @lem3302980 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302041 _86426 q x' h1)). Qed.
Lemma lem3303022 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : q x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3303021 _86426 p q r x' h1 h2) (@lem3302041 _86426 q x' h1)). Qed.
Lemma lem3303023 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : (p x') = False.
Proof. exact (prop_ext (fun h3 : p x' => @lem3302982 _86426 p q r x' h1 h2) (fun h3 : False => @lem3302025 _86426 p x' h1)). Qed.
Lemma lem3303024 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : p x') (h2 : term341 _86426 p q r x') : False.
Proof. exact (EQ_MP (@lem3303023 _86426 p q r x' h1 h2) (@lem3302025 _86426 p x' h1)). Qed.
Lemma lem3303025 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : (p x) = False.
Proof. exact (prop_ext (fun h3 : p x => @lem3302984 _86426 q p x h1 h2) (fun h3 : False => @lem3302009 _86426 p x h1)). Qed.
Lemma lem3303026 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3303025 _86426 q p x h1 h2) (@lem3302009 _86426 p x h1)). Qed.
Lemma lem3303027 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : (q x) = False.
Proof. exact (prop_ext (fun h3 : q x => @lem3302986 _86426 q p x h1 h2) (fun h3 : False => @lem3301997 _86426 q x h1)). Qed.
Lemma lem3303028 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term295 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3303027 _86426 q p x h1 h2) (@lem3301997 _86426 q x h1)). Qed.
Lemma lem3303029 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : (q x) = False.
Proof. exact (prop_ext (fun h3 : q x => @lem3302988 _86426 q p x h1 h2) (fun h3 : False => @lem3301985 _86426 q x h1)). Qed.
Lemma lem3303030 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : q x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3303029 _86426 q p x h1 h2) (@lem3301985 _86426 q x h1)). Qed.
Lemma lem3303031 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : (p x) = False.
Proof. exact (prop_ext (fun h3 : p x => @lem3302990 _86426 q p x h1 h2) (fun h3 : False => @lem3301973 _86426 p x h1)). Qed.
Lemma lem3303032 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : p x) (h2 : term298 _86426 q p x) : False.
Proof. exact (EQ_MP (@lem3303031 _86426 q p x h1 h2) (@lem3301973 _86426 p x h1)). Qed.
Lemma lem3303033 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term415 _86426 p q x') : False.
Proof. exact (or_elim (@lem3301954 _86426 p q x' h1) (fun h0 : p x' => @lem3302994 _86426 p q x' h0 h1) (fun h0 : q x' => @lem3302992 _86426 p q x' h0 h1)). Qed.
Lemma lem3303034 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') (h2 : term29 _86426 p q x') : False.
Proof. exact (or_elim (@lem3301951 _86426 p q x' h2) (fun h0 : p x' => @lem3302998 _86426 p q x' h0 h1) (fun h0 : q x' => @lem3302996 _86426 p q x' h0 h1)). Qed.
Lemma lem3303035 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term418 _86426 p q x') : False.
Proof. exact (or_elim (@lem3301947 _86426 p q x' h1) (fun h0 : p x' => @lem3303000 _86426 p q x' h0 h1) (fun h0 : term29 _86426 p q x' => @lem3303034 _86426 p q x' h1 h0)). Qed.
Lemma lem3303036 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term422 _86426 p q x') : False.
Proof. exact (or_elim (@lem3301921 _86426 p q x' h1) (fun h0 : term418 _86426 p q x' => @lem3303035 _86426 p q x' h0) (fun h0 : term415 _86426 p q x' => @lem3303033 _86426 p q x' h0)). Qed.
Lemma lem3303037 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') (h2 : term29 _86426 p r x') : False.
Proof. exact (or_elim (@lem3301941 _86426 p r x' h2) (fun h0 : p x' => @lem3303004 _86426 q p r x' h0 h1) (fun h0 : r x' => @lem3303002 _86426 q p r x' h0 h1)). Qed.
Lemma lem3303038 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term375 _86426 q p r x') : False.
Proof. exact (or_elim (@lem3301934 _86426 q p r x' h1) (fun h0 : q x' => @lem3303006 _86426 q p r x' h0 h1) (fun h0 : term29 _86426 p r x' => @lem3303037 _86426 q p r x' h1 h0)). Qed.
Lemma lem3303039 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') (h2 : term29 _86426 q r x') : False.
Proof. exact (or_elim (@lem3301931 _86426 q r x' h2) (fun h0 : q x' => @lem3303010 _86426 q p r x' h0 h1) (fun h0 : r x' => @lem3303008 _86426 q p r x' h0 h1)). Qed.
Lemma lem3303040 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term378 _86426 q p r x') : False.
Proof. exact (or_elim (@lem3301925 _86426 q p r x' h1) (fun h0 : p x' => @lem3303012 _86426 q p r x' h0 h1) (fun h0 : term29 _86426 q r x' => @lem3303039 _86426 p q r x' h1 h0)). Qed.
Lemma lem3303041 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term382 _86426 q p r x') : False.
Proof. exact (or_elim (@lem3301920 _86426 q p r x' h1) (fun h0 : term378 _86426 q p r x' => @lem3303040 _86426 q p r x' h0) (fun h0 : term375 _86426 q p r x' => @lem3303038 _86426 q p r x' h0)). Qed.
Lemma lem3303042 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term864 _86426 r p q x') : False.
Proof. exact (or_elim (@lem3301897 _86426 r p q x' h1) (fun h0 : term382 _86426 q p r x' => @lem3303041 _86426 q p r x' h0) (fun h0 : term422 _86426 p q x' => @lem3303036 _86426 p q x' h0)). Qed.
Lemma lem3303043 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') (h2 : term29 _86426 q r x') : False.
Proof. exact (or_elim (@lem3301917 _86426 q r x' h2) (fun h0 : q x' => @lem3303016 _86426 p q r x' h0 h1) (fun h0 : r x' => @lem3303014 _86426 p q r x' h0 h1)). Qed.
Lemma lem3303044 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term338 _86426 p q r x') : False.
Proof. exact (or_elim (@lem3301910 _86426 p q r x' h1) (fun h0 : p x' => @lem3303018 _86426 p q r x' h0 h1) (fun h0 : term29 _86426 q r x' => @lem3303043 _86426 p q r x' h1 h0)). Qed.
Lemma lem3303045 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') (h2 : term29 _86426 p q x') : False.
Proof. exact (or_elim (@lem3301906 _86426 p q x' h2) (fun h0 : p x' => @lem3303024 _86426 p q r x' h0 h1) (fun h0 : q x' => @lem3303022 _86426 p q r x' h0 h1)). Qed.
Lemma lem3303046 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term341 _86426 p q r x') : False.
Proof. exact (or_elim (@lem3301901 _86426 p q r x' h1) (fun h0 : term29 _86426 p q x' => @lem3303045 _86426 r p q x' h1 h0) (fun h0 : r x' => @lem3303020 _86426 p q r x' h0 h1)). Qed.
Lemma lem3303047 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) (x' : _86426) (h1 : term345 _86426 p q r x') : False.
Proof. exact (or_elim (@lem3301896 _86426 p q r x' h1) (fun h0 : term341 _86426 p q r x' => @lem3303046 _86426 p q r x' h0) (fun h0 : term338 _86426 p q r x' => @lem3303044 _86426 p q r x' h0)). Qed.
Lemma lem3303048 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term943 _86426 r p q x') : False.
Proof. exact (or_elim (@lem3301881 _86426 r p q x' h1) (fun h0 : term345 _86426 p q r x' => @lem3303047 _86426 p q r x' h0) (fun h0 : term864 _86426 r p q x' => @lem3303042 _86426 r p q x' h0)). Qed.
Lemma lem3303049 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term295 _86426 q p x) : False.
Proof. exact (or_elim (@lem3301890 _86426 q p x h1) (fun h0 : q x => @lem3303028 _86426 q p x h0 h1) (fun h0 : p x => @lem3303026 _86426 q p x h0 h1)). Qed.
Lemma lem3303050 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term298 _86426 q p x) : False.
Proof. exact (or_elim (@lem3301885 _86426 q p x h1) (fun h0 : p x => @lem3303032 _86426 q p x h0 h1) (fun h0 : q x => @lem3303030 _86426 q p x h0 h1)). Qed.
Lemma lem3303051 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) (x : _86426) (h1 : term302 _86426 q p x) : False.
Proof. exact (or_elim (@lem3301880 _86426 q p x h1) (fun h0 : term298 _86426 q p x => @lem3303050 _86426 q p x h0) (fun h0 : term295 _86426 q p x => @lem3303049 _86426 q p x h0)). Qed.
Lemma lem3303052 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term1029 _86426 x r p q x') : False.
Proof. exact (or_elim (@lem3301879 _86426 x r p q x' h1) (fun h0 : term302 _86426 q p x => @lem3303051 _86426 q p x h0) (fun h0 : term943 _86426 r p q x' => @lem3303048 _86426 r p q x' h0)). Qed.
Lemma lem3303053 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term1029 _86426 x r p q x') : (term1029 _86426 x r p q x') = False.
Proof. exact (prop_ext (fun h2 : term1029 _86426 x r p q x' => @lem3303052 _86426 x r p q x' h1) (fun h2 : False => @lem3301879 _86426 x r p q x' h1)). Qed.
Lemma lem3303054 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (x' : _86426) (h1 : term1029 _86426 x r p q x') : False.
Proof. exact (EQ_MP (@lem3303053 _86426 x r p q x' h1) (@lem3301879 _86426 x r p q x' h1)). Qed.
Lemma lem3303055 {_86426 : Type'} (x : _86426) (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term1032 _86426 x r p q) : False.
Proof. exact (ex_elim (@lem3301586 _86426 x r p q h1) (fun x' : _86426 => fun h0 : term1031 _86426 x r p q x' => @lem3303054 _86426 x r p q x' h0)). Qed.
Lemma lem3303056 {_86426 : Type'} (x : _86426) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term1034 _86426 x p q) : False.
Proof. exact (ex_elim (@lem3301585 _86426 x p q h1) (fun r : _86426 -> Prop => fun h0 : term1033 _86426 x p q r => @lem3303055 _86426 x r p q h0)). Qed.
Lemma lem3303057 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term1036 _86426 p q) : False.
Proof. exact (ex_elim (@lem3301584 _86426 p q h1) (fun x : _86426 => fun h0 : term1035 _86426 p q x => @lem3303056 _86426 x p q h0)). Qed.
Lemma lem3303058 {_86426 : Type'} (q : _86426 -> Prop) (h1 : term1038 _86426 q) : False.
Proof. exact (ex_elim (@lem3301583 _86426 q h1) (fun p : _86426 -> Prop => fun h0 : term1037 _86426 q p => @lem3303057 _86426 p q h0)). Qed.
Lemma lem3303059 {_86426 : Type'} (h1 : term289 _86426) : False.
Proof. exact (ex_elim (@lem3301582 _86426 h1) (fun q : _86426 -> Prop => fun h0 : term1039 _86426 q => @lem3303058 _86426 q h0)). Qed.
Lemma lem3303060 {_86426 : Type'} (h1 : term289 _86426) : (term289 _86426) = False.
Proof. exact (prop_ext (fun h2 : term289 _86426 => @lem3303059 _86426 h1) (fun h2 : False => @lem3298474 _86426 h1)). Qed.
Lemma lem3303061 {_86426 : Type'} (h1 : term289 _86426) : False.
Proof. exact (EQ_MP (@lem3303060 _86426 h1) (@lem3298474 _86426 h1)). Qed.
Lemma lem3303062 {_86426 : Type'} : term288 _86426.
Proof. exact (fun h0 : term289 _86426 => @lem3303061 _86426 h0). Qed.
Lemma lem3303063 {_86426 : Type'} : term287 _86426.
Proof. exact (EQ_MP (@lem3298473 _86426) (@lem3303062 _86426)). Qed.
Lemma lem3303064 {_86426 : Type'} : term224 _86426.
Proof. exact (EQ_MP (@lem3298469 _86426) (@lem3303063 _86426)). Qed.
Lemma lem3303065 {_86426 : Type'} (q : _86426 -> Prop) : term1045 _86426 q.
Proof. exact (@lem3303064 _86426 q). Qed.
Lemma lem3303066 {_86426 : Type'} (q : _86426 -> Prop) : (term1045 _86426 q) = (term158 _86426 q).
Proof. exact (eq_refl (term1045 _86426 q)). Qed.
Lemma lem3303067 {_86426 : Type'} (q : _86426 -> Prop) : term158 _86426 q.
Proof. exact (EQ_MP (@lem3303066 _86426 q) (@lem3303065 _86426 q)). Qed.
Lemma lem3303068 {_86426 : Type'} (q : _86426 -> Prop) (p : _86426 -> Prop) : term1046 _86426 q p.
Proof. exact (@lem3303067 _86426 q p). Qed.
Lemma lem3303069 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1046 _86426 q p) = (term86 _86426 p q).
Proof. exact (eq_refl (term1046 _86426 q p)). Qed.
Lemma lem3303070 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) : term86 _86426 p q.
Proof. exact (EQ_MP (@lem3303069 _86426 p q) (@lem3303068 _86426 q p)). Qed.
Lemma lem3303071 {_86426 : Type'} (p : _86426 -> Prop) (q : _86426 -> Prop) (r : _86426 -> Prop) : term1047 _86426 p q r.
Proof. exact (@lem3303070 _86426 p q r). Qed.
Lemma lem3303072 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : (term1047 _86426 p q r) = (term77 _86426 r p q).
Proof. exact (eq_refl (term1047 _86426 p q r)). Qed.
Lemma lem3303073 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term77 _86426 r p q.
Proof. exact (EQ_MP (@lem3303072 _86426 r p q) (@lem3303071 _86426 p q r)). Qed.
Lemma lem3303075 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term77 _86426 r p q.
Proof. exact (@lem3297640 _86426 r p q (@lem3303073 _86426 r p q)). Qed.
Lemma lem3303076 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term78 _86426 r p q) : False.
Proof. exact (@lem3303075 _86426 r p q (@lem3297624 _86426 r p q h1)). Qed.
Lemma lem3303077 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term78 _86426 r p q) : (term78 _86426 r p q) = False.
Proof. exact (prop_ext (fun h2 : term78 _86426 r p q => @lem3303076 _86426 r p q h1) (fun h2 : False => @lem3297624 _86426 r p q h1)). Qed.
Lemma lem3303078 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) (h1 : term78 _86426 r p q) : False.
Proof. exact (EQ_MP (@lem3303077 _86426 r p q h1) (@lem3297624 _86426 r p q h1)). Qed.
Lemma lem3303079 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term77 _86426 r p q.
Proof. exact (fun h0 : term78 _86426 r p q => @lem3303078 _86426 r p q h0). Qed.
Lemma lem3303080 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term75 _86426 r p q.
Proof. exact (EQ_MP (@lem3297623 _86426 r p q) (@lem3303079 _86426 r p q)). Qed.
Lemma lem3303081 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term24 _86426 r p q.
Proof. exact (EQ_MP (@lem3297619 _86426 r p q) (@lem3303080 _86426 r p q)). Qed.
Lemma lem3303082 {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop) : term23 _86426 r p q.
Proof. exact (EQ_MP (@lem3297225 _86426 r p q) (@lem3303081 _86426 r p q)). Qed.
