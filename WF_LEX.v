Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_LEX_term_abbrevs.
Require Import ETA_AX_spec.
Require Import WF_LEX_DEPENDENT_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem364171 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem364172 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem364173 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem364172 A B t) (@lem364171 A B t)). Qed.
Lemma lem364174 {A B : Type'} (R : type1402 A) : term2 A B R.
Proof. exact (@lem364170 A B R). Qed.
Lemma lem364175 {A B : Type'} (R : type1402 A) : (term2 A B R) = (term3 A B R).
Proof. exact (eq_refl (term2 A B R)). Qed.
Lemma lem364176 {A B : Type'} (R : type1402 A) : term3 A B R.
Proof. exact (EQ_MP (@lem364175 A B R) (@lem364174 A B R)). Qed.
Lemma lem364177 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term4 A B R S'.
Proof. exact (@lem364176 A B R S'). Qed.
Lemma lem364178 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term4 A B R S') = (term5 A B R S').
Proof. exact (eq_refl (term4 A B R S')). Qed.
Lemma lem364179 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term5 A B R S'.
Proof. exact (EQ_MP (@lem364178 A B R S') (@lem364177 A B R S')). Qed.
Lemma lem364180 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term6 A B R S') : term6 A B R S'.
Proof. exact (h1). Qed.
Lemma lem364181 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term6 A B R S') : term7 A B R S'.
Proof. exact (@lem364179 A B R S' (@lem364180 A B R S' h1)). Qed.
Lemma lem364182 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term7 A B R S') = ((term7 A B R S') = True).
Proof. exact (@lem7 (term7 A B R S')). Qed.
Lemma lem364183 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term6 A B R S') : (term7 A B R S') = True.
Proof. exact (EQ_MP (@lem364182 A B R S') (@lem364181 A B R S' h1)). Qed.
Lemma lem364200 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem364201 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem364200 p q p' q'). Qed.
Lemma lem364202 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem364201 p q p'). Qed.
Lemma lem364203 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term11 A B R S'.
Proof. exact (@lem364202 (term12 A B R S') (term13 A B R S')). Qed.
Lemma lem364204 {A B : Type'} (R : type1402 A) (S' : type1402 B) (p' : Prop) : term14 A B R S' p'.
Proof. exact (@lem364203 A B R S' p'). Qed.
Lemma lem364205 {A B : Type'} (R : type1402 A) (S' : type1402 B) (p' : Prop) : (term14 A B R S' p') = (term15 A B R S' p').
Proof. exact (eq_refl (term14 A B R S' p')). Qed.
Lemma lem364206 {A B : Type'} (R : type1402 A) (S' : type1402 B) (p' : Prop) : term15 A B R S' p'.
Proof. exact (EQ_MP (@lem364205 A B R S' p') (@lem364204 A B R S' p')). Qed.
Lemma lem364207 {A B : Type'} (R : type1402 A) (S' : type1402 B) (p' : Prop) (q' : Prop) : term16 A B R S' p' q'.
Proof. exact (@lem364206 A B R S' p' q'). Qed.
Lemma lem364208 {A B : Type'} (R : type1402 A) (S' : type1402 B) (p' : Prop) (q' : Prop) : (term16 A B R S' p' q') = (term17 A B R S' p' q').
Proof. exact (eq_refl (term16 A B R S' p' q')). Qed.
Lemma lem364209 {A B : Type'} (R : type1402 A) (S' : type1402 B) (p' : Prop) (q' : Prop) : term17 A B R S' p' q'.
Proof. exact (EQ_MP (@lem364208 A B R S' p' q') (@lem364207 A B R S' p' q')). Qed.
Lemma lem364212 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term12 A B R S') = (term12 A B R S').
Proof. exact (eq_refl (term12 A B R S')). Qed.
Lemma lem364213 {A B : Type'} (R : type1402 A) (S' : type1402 B) (q' : Prop) : term18 A B R S' q'.
Proof. exact (@lem364209 A B R S' (term12 A B R S') q'). Qed.
Lemma lem364214 {A B : Type'} (R : type1402 A) (S' : type1402 B) (q' : Prop) : term19 A B R S' q'.
Proof. exact (@lem364213 A B R S' q' (@lem364212 A B R S')). Qed.
Lemma lem364215 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : term12 A B R S'.
Proof. exact (h1). Qed.
Lemma lem364216 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : @WF B S'.
Proof. exact (proj2 (@lem364215 A B R S' h1)). Qed.
Lemma lem364217 {B : Type'} (S' : type1402 B) : (@WF B S') = ((@WF B S') = True).
Proof. exact (@lem7 (@WF B S')). Qed.
Lemma lem364219 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : @WF A R.
Proof. exact (proj1 (@lem364215 A B R S' h1)). Qed.
Lemma lem364220 {A : Type'} (R : type1402 A) : (@WF A R) = ((@WF A R) = True).
Proof. exact (@lem7 (@WF A R)). Qed.
Lemma lem364223 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term20 A B R S'.
Proof. exact (fun h0 : term6 A B R S' => @lem364183 A B R S' h0). Qed.
Lemma lem364224 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term20 A B R S'.
Proof. exact (@lem364223 A B R S'). Qed.
Lemma lem364225 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term21 A B R S'.
Proof. exact (@lem364224 A B R (term22 A B S')). Qed.
Lemma lem364226 {A B : Type'} (r1 : A) (S' : type1402 B) : (term23 A B S' r1) = (term24 B S').
Proof. exact (eq_refl (term23 A B S' r1)). Qed.
Lemma lem364227 {B : Type'} (s1 : B) : s1 = s1.
Proof. exact (eq_refl s1). Qed.
Lemma lem364228 {A B : Type'} (r1 : A) (S' : type1402 B) (s1 : B) : (term25 A B S' r1 s1) = (term26 B S' s1).
Proof. exact (MK_COMB (@lem364226 A B r1 S') (@lem364227 B s1)). Qed.
Lemma lem364229 {B : Type'} (S' : type1402 B) (s1 : B) : (term26 B S' s1) = (term27 B S' s1).
Proof. exact (eq_refl (term26 B S' s1)). Qed.
Lemma lem364230 {A B : Type'} (r1 : A) (S' : type1402 B) (s1 : B) : (term25 A B S' r1 s1) = (term27 B S' s1).
Proof. exact (TRANS (@lem364228 A B r1 S' s1) (@lem364229 B S' s1)). Qed.
Lemma lem364231 {B : Type'} (s2 : B) : s2 = s2.
Proof. exact (eq_refl s2). Qed.
Lemma lem364232 {A B : Type'} (r1 : A) (S' : type1402 B) (s1 : B) (s2 : B) : (term28 A B S' r1 s1 s2) = (term29 B S' s1 s2).
Proof. exact (MK_COMB (@lem364230 A B r1 S' s1) (@lem364231 B s2)). Qed.
Lemma lem364233 {B : Type'} (S' : type1402 B) (s1 : B) (s2 : B) : (term29 B S' s1 s2) = (S' s1 s2).
Proof. exact (eq_refl (term29 B S' s1 s2)). Qed.
Lemma lem364234 {A B : Type'} (r1 : A) (S' : type1402 B) (s1 : B) (s2 : B) : (term28 A B S' r1 s1 s2) = (S' s1 s2).
Proof. exact (TRANS (@lem364232 A B r1 S' s1 s2) (@lem364233 B S' s1 s2)). Qed.
Lemma lem364235 {A : Type'} (r1 : A) (r2 : A) : (term30 A r1 r2) = (term30 A r1 r2).
Proof. exact (eq_refl (term30 A r1 r2)). Qed.
Lemma lem364236 {A B : Type'} (r1 : A) (r2 : A) (S' : type1402 B) (s1 : B) (s2 : B) : (term31 A B r2 S' r1 s1 s2) = (term32 A B r1 r2 S' s1 s2).
Proof. exact (MK_COMB (@lem364235 A r1 r2) (@lem364234 A B r1 S' s1 s2)). Qed.
Lemma lem364237 {A : Type'} (R : type1402 A) (r1 : A) (r2 : A) : (term33 A R r1 r2) = (term33 A R r1 r2).
Proof. exact (eq_refl (term33 A R r1 r2)). Qed.
Lemma lem364238 {A B : Type'} (R : type1402 A) (r1 : A) (r2 : A) (S' : type1402 B) (s1 : B) (s2 : B) : (term34 A B R r2 S' r1 s1 s2) = (term35 A B R r1 r2 S' s1 s2).
Proof. exact (MK_COMB (@lem364237 A R r1 r2) (@lem364236 A B r1 r2 S' s1 s2)). Qed.
Lemma lem364239 {A B : Type'} (f : type1210 A B) (r2 : A) (s2 : B) : (term36 A B f r2 s2) = (term36 A B f r2 s2).
Proof. exact (eq_refl (term36 A B f r2 s2)). Qed.
Lemma lem364240 {A B : Type'} (f : type1210 A B) (R : type1402 A) (r1 : A) (r2 : A) (S' : type1402 B) (s1 : B) (s2 : B) : (term37 A B f R r2 S' r1 s1 s2) = (term38 A B f R r1 r2 S' s1 s2).
Proof. exact (MK_COMB (@lem364239 A B f r2 s2) (@lem364238 A B R r1 r2 S' s1 s2)). Qed.
Lemma lem364241 {A B : Type'} (f : type1210 A B) (R : type1402 A) (r1 : A) (r2 : A) (S' : type1402 B) (s1 : B) : (term39 A B f R r2 S' r1 s1) = (term40 A B f R r1 r2 S' s1).
Proof. exact (fun_ext (fun s2 : B => @lem364240 A B f R r1 r2 S' s1 s2)). Qed.
Lemma lem364242 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364243 {A B : Type'} (f : type1210 A B) (R : type1402 A) (r1 : A) (r2 : A) (S' : type1402 B) (s1 : B) : (term41 A B f R r2 S' r1 s1) = (term42 A B f R r1 r2 S' s1).
Proof. exact (MK_COMB (@lem364242 B) (@lem364241 A B f R r1 r2 S' s1)). Qed.
Lemma lem364244 {A B : Type'} (f : type1210 A B) (R : type1402 A) (r1 : A) (S' : type1402 B) (s1 : B) : (term43 A B f R S' r1 s1) = (term44 A B f R r1 S' s1).
Proof. exact (fun_ext (fun r2 : A => @lem364243 A B f R r1 r2 S' s1)). Qed.
Lemma lem364245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364246 {A B : Type'} (f : type1210 A B) (R : type1402 A) (r1 : A) (S' : type1402 B) (s1 : B) : (term45 A B f R S' r1 s1) = (term46 A B f R r1 S' s1).
Proof. exact (MK_COMB (@lem364245 A) (@lem364244 A B f R r1 S' s1)). Qed.
Lemma lem364247 {A B : Type'} (R : type1402 A) (r1 : A) (S' : type1402 B) (s1 : B) : (term47 A B R S' r1 s1) = (term48 A B R r1 S' s1).
Proof. exact (fun_ext (fun f : type1210 A B => @lem364246 A B f R r1 S' s1)). Qed.
Lemma lem364248 {A B : Type'} : (@GABS ((prod A B) -> Prop)) = (@GABS ((prod A B) -> Prop)).
Proof. exact (eq_refl (@GABS ((prod A B) -> Prop))). Qed.
Lemma lem364249 {A B : Type'} (R : type1402 A) (r1 : A) (S' : type1402 B) (s1 : B) : (term49 A B R S' r1 s1) = (term50 A B R r1 S' s1).
Proof. exact (MK_COMB (@lem364248 A B) (@lem364247 A B R r1 S' s1)). Qed.
Lemma lem364250 {A B : Type'} (f : type1204 A B) (r1 : A) (s1 : B) : (term51 A B f r1 s1) = (term51 A B f r1 s1).
Proof. exact (eq_refl (term51 A B f r1 s1)). Qed.
Lemma lem364251 {A B : Type'} (f : type1204 A B) (R : type1402 A) (r1 : A) (S' : type1402 B) (s1 : B) : (term52 A B f R S' r1 s1) = (term53 A B f R r1 S' s1).
Proof. exact (MK_COMB (@lem364250 A B f r1 s1) (@lem364249 A B R r1 S' s1)). Qed.
Lemma lem364252 {A B : Type'} (f : type1204 A B) (R : type1402 A) (r1 : A) (S' : type1402 B) : (term54 A B f R S' r1) = (term55 A B f R r1 S').
Proof. exact (fun_ext (fun s1 : B => @lem364251 A B f R r1 S' s1)). Qed.
Lemma lem364253 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364254 {A B : Type'} (f : type1204 A B) (R : type1402 A) (r1 : A) (S' : type1402 B) : (term56 A B f R S' r1) = (term57 A B f R r1 S').
Proof. exact (MK_COMB (@lem364253 B) (@lem364252 A B f R r1 S')). Qed.
Lemma lem364255 {A B : Type'} (f : type1204 A B) (R : type1402 A) (S' : type1402 B) : (term58 A B f R S') = (term59 A B f R S').
Proof. exact (fun_ext (fun r1 : A => @lem364254 A B f R r1 S')). Qed.
Lemma lem364256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364257 {A B : Type'} (f : type1204 A B) (R : type1402 A) (S' : type1402 B) : (term60 A B f R S') = (term61 A B f R S').
Proof. exact (MK_COMB (@lem364256 A) (@lem364255 A B f R S')). Qed.
Lemma lem364258 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term62 A B R S') = (term63 A B R S').
Proof. exact (fun_ext (fun f : type1204 A B => @lem364257 A B f R S')). Qed.
Lemma lem364259 {A B : Type'} : (@GABS ((prod A B) -> (prod A B) -> Prop)) = (@GABS ((prod A B) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@GABS ((prod A B) -> (prod A B) -> Prop))). Qed.
Lemma lem364260 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term64 A B R S') = (term65 A B R S').
Proof. exact (MK_COMB (@lem364259 A B) (@lem364258 A B R S')). Qed.
Lemma lem364261 {A B : Type'} : (@WF (prod A B)) = (@WF (prod A B)).
Proof. exact (eq_refl (@WF (prod A B))). Qed.
Lemma lem364262 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term66 A B R S') = (term13 A B R S').
Proof. exact (MK_COMB (@lem364261 A B) (@lem364260 A B R S')). Qed.
Lemma lem364263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem364264 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term67 A B R S') = (term68 A B R S').
Proof. exact (MK_COMB (@lem364263) (@lem364262 A B R S')). Qed.
Lemma lem364265 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem364266 {A B : Type'} (R : type1402 A) (S' : type1402 B) : ((term66 A B R S') = True) = ((term13 A B R S') = True).
Proof. exact (MK_COMB (@lem364264 A B R S') (@lem364265)). Qed.
Lemma lem364267 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term69 A B R S') = (term69 A B R S').
Proof. exact (eq_refl (term69 A B R S')). Qed.
Lemma lem364268 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term21 A B R S') = (term70 A B R S').
Proof. exact (MK_COMB (@lem364267 A B R S') (@lem364266 A B R S')). Qed.
Lemma lem364269 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term70 A B R S'.
Proof. exact (EQ_MP (@lem364268 A B R S') (@lem364225 A B R S')). Qed.
Lemma lem364273 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (@WF A R) = True.
Proof. exact (EQ_MP (@lem364220 A R) (@lem364219 A B R S' h1)). Qed.
Lemma lem364274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem364275 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term71 A R) = (and True).
Proof. exact (MK_COMB (@lem364274) (@lem364273 A B R S' h1)). Qed.
Lemma lem364281 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem364282 {A B : Type'} (f : type1406 A B) (y : A) : (term73 A B f y) = (f y).
Proof. exact (@lem364281 A (type1402 B) f y). Qed.
Lemma lem364283 {A B : Type'} (S' : type1402 B) (a : A) : (term74 A B S' a) = (term23 A B S' a).
Proof. exact (@lem364282 A B (term22 A B S') a). Qed.
Lemma lem364284 {A B : Type'} (r1 : A) (S' : type1402 B) : (term23 A B S' r1) = (term24 B S').
Proof. exact (eq_refl (term23 A B S' r1)). Qed.
Lemma lem364285 {A B : Type'} (S' : type1402 B) : (term75 A B S') = (term22 A B S').
Proof. exact (fun_ext (fun r1 : A => @lem364284 A B r1 S')). Qed.
Lemma lem364286 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem364287 {A B : Type'} (S' : type1402 B) (a : A) : (term74 A B S' a) = (term23 A B S' a).
Proof. exact (MK_COMB (@lem364285 A B S') (@lem364286 A a)). Qed.
Lemma lem364288 {B : Type'} : (@eq (B -> B -> Prop)) = (@eq (B -> B -> Prop)).
Proof. exact (eq_refl (@eq (B -> B -> Prop))). Qed.
Lemma lem364289 {A B : Type'} (S' : type1402 B) (a : A) : (term76 A B S' a) = (term77 A B S' a).
Proof. exact (MK_COMB (@lem364288 B) (@lem364287 A B S' a)). Qed.
Lemma lem364290 {A B : Type'} (a : A) (S' : type1402 B) : (term23 A B S' a) = (term24 B S').
Proof. exact (eq_refl (term23 A B S' a)). Qed.
Lemma lem364291 {A B : Type'} (a : A) (S' : type1402 B) : ((term74 A B S' a) = (term23 A B S' a)) = ((term23 A B S' a) = (term24 B S')).
Proof. exact (MK_COMB (@lem364289 A B S' a) (@lem364290 A B a S')). Qed.
Lemma lem364292 {A B : Type'} (a : A) (S' : type1402 B) : (term23 A B S' a) = (term24 B S').
Proof. exact (EQ_MP (@lem364291 A B a S') (@lem364283 A B S' a)). Qed.
Lemma lem364293 {B : Type'} (t : B -> Prop) : (term78 B t) = t.
Proof. exact (@lem364173 B Prop t). Qed.
Lemma lem364294 {B : Type'} (S' : type1402 B) (s1 : B) : (term27 B S' s1) = (S' s1).
Proof. exact (@lem364293 B (S' s1)). Qed.
Lemma lem364295 {B : Type'} (S' : type1402 B) : (term24 B S') = (term79 B S').
Proof. exact (fun_ext (fun s1 : B => @lem364294 B S' s1)). Qed.
Lemma lem364296 {B : Type'} (t : type1402 B) : (term79 B t) = t.
Proof. exact (@lem364173 B (B -> Prop) t). Qed.
Lemma lem364297 {B : Type'} (S' : type1402 B) : (term79 B S') = S'.
Proof. exact (@lem364296 B S'). Qed.
Lemma lem364298 {B : Type'} (S' : type1402 B) : (term24 B S') = S'.
Proof. exact (TRANS (@lem364295 B S') (@lem364297 B S')). Qed.
Lemma lem364299 {A B : Type'} (a : A) (S' : type1402 B) : (term23 A B S' a) = S'.
Proof. exact (TRANS (@lem364292 A B a S') (@lem364298 B S')). Qed.
Lemma lem364300 {B : Type'} : (@WF B) = (@WF B).
Proof. exact (eq_refl (@WF B)). Qed.
Lemma lem364301 {A B : Type'} (a : A) (S' : type1402 B) : (term80 A B S' a) = (@WF B S').
Proof. exact (MK_COMB (@lem364300 B) (@lem364299 A B a S')). Qed.
Lemma lem364303 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (@WF B S') = True.
Proof. exact (EQ_MP (@lem364217 B S') (@lem364216 A B R S' h1)). Qed.
Lemma lem364304 {A B : Type'} (a : A) (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term80 A B S' a) = True.
Proof. exact (TRANS (@lem364301 A B a S') (@lem364303 A B R S' h1)). Qed.
Lemma lem364305 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term81 A B S') = (term82 A).
Proof. exact (fun_ext (fun a : A => @lem364304 A B a R S' h1)). Qed.
Lemma lem364306 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364307 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term83 A B S') = (term84 A).
Proof. exact (MK_COMB (@lem364306 A) (@lem364305 A B R S' h1)). Qed.
Lemma lem364309 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem364310 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem364309 A t). Qed.
Lemma lem364311 {A : Type'} : (term84 A) = True.
Proof. exact (@lem364310 A True). Qed.
Lemma lem364312 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term83 A B S') = True.
Proof. exact (TRANS (@lem364307 A B R S' h1) (@lem364311 A)). Qed.
Lemma lem364313 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term86 A B R S') = (True /\ True).
Proof. exact (MK_COMB (@lem364275 A B R S' h1) (@lem364312 A B R S' h1)). Qed.
Lemma lem364315 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem364316 : (True /\ True) = True.
Proof. exact (@lem364315 True). Qed.
Lemma lem364317 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term86 A B R S') = True.
Proof. exact (TRANS (@lem364313 A B R S' h1) (@lem364316)). Qed.
Lemma lem364318 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : True = (term86 A B R S').
Proof. exact (SYM (@lem364317 A B R S' h1)). Qed.
Lemma lem364319 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : term86 A B R S'.
Proof. exact (EQ_MP (@lem364318 A B R S' h1) (@lem0)). Qed.
Lemma lem364320 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term12 A B R S') : (term13 A B R S') = True.
Proof. exact (@lem364269 A B R S' (@lem364319 A B R S' h1)). Qed.
Lemma lem364321 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term87 A B R S'.
Proof. exact (fun h0 : term12 A B R S' => @lem364320 A B R S' h0). Qed.
Lemma lem364322 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term88 A B R S'.
Proof. exact (@lem364214 A B R S' True). Qed.
Lemma lem364323 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term89 A B R S') = (term90 A B R S').
Proof. exact (@lem364322 A B R S' (@lem364321 A B R S')). Qed.
Lemma lem364325 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem364326 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term90 A B R S') = True.
Proof. exact (@lem364325 (term12 A B R S')). Qed.
Lemma lem364327 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term89 A B R S') = True.
Proof. exact (TRANS (@lem364323 A B R S') (@lem364326 A B R S')). Qed.
Lemma lem364328 {A B : Type'} (R : type1402 A) : (term91 A B R) = (term92 B).
Proof. exact (fun_ext (fun S' : type1402 B => @lem364327 A B R S')). Qed.
Lemma lem364329 {B : Type'} : (@all (B -> B -> Prop)) = (@all (B -> B -> Prop)).
Proof. exact (eq_refl (@all (B -> B -> Prop))). Qed.
Lemma lem364330 {A B : Type'} (R : type1402 A) : (term93 A B R) = (term94 B).
Proof. exact (MK_COMB (@lem364329 B) (@lem364328 A B R)). Qed.
Lemma lem364332 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem364333 {B : Type'} (t : Prop) : (term95 B t) = t.
Proof. exact (@lem364332 (type1402 B) t). Qed.
Lemma lem364334 {B : Type'} : (term94 B) = True.
Proof. exact (@lem364333 B True). Qed.
Lemma lem364335 {A B : Type'} (R : type1402 A) : (term93 A B R) = True.
Proof. exact (TRANS (@lem364330 A B R) (@lem364334 B)). Qed.
Lemma lem364336 {A B : Type'} : (term96 A B) = (term92 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem364335 A B R)). Qed.
Lemma lem364337 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem364338 {A B : Type'} : (term97 A B) = (term94 A).
Proof. exact (MK_COMB (@lem364337 A) (@lem364336 A B)). Qed.
Lemma lem364340 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem364341 {A : Type'} (t : Prop) : (term95 A t) = t.
Proof. exact (@lem364340 (type1402 A) t). Qed.
Lemma lem364342 {A : Type'} : (term94 A) = True.
Proof. exact (@lem364341 A True). Qed.
Lemma lem364343 {A B : Type'} : (term97 A B) = True.
Proof. exact (TRANS (@lem364338 A B) (@lem364342 A)). Qed.
Lemma lem364344 {A B : Type'} : True = (term97 A B).
Proof. exact (SYM (@lem364343 A B)). Qed.
Lemma lem364345 {A B : Type'} : term97 A B.
Proof. exact (EQ_MP (@lem364344 A B) (@lem0)). Qed.
