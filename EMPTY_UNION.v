Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_UNION_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3236073 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3236074 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3236073 A s t). Qed.
Lemma lem3236075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@UNION A s t) = (@EMPTY A)) = (term1 A s t).
Proof. exact (@lem3236074 A (@UNION A s t) (@EMPTY A)). Qed.
Lemma lem3236084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236085 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3236084) (@lem3236075 A s t)). Qed.
Lemma lem3236091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3236092 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3236091 A s t). Qed.
Lemma lem3236093 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term4 A s).
Proof. exact (@lem3236092 A s (@EMPTY A)). Qed.
Lemma lem3236102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236103 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3236102) (@lem3236093 A s)). Qed.
Lemma lem3236107 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3236108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3236107 A s t). Qed.
Lemma lem3236109 {A : Type'} (t : A -> Prop) : (t = (@EMPTY A)) = (term4 A t).
Proof. exact (@lem3236108 A t (@EMPTY A)). Qed.
Lemma lem3236118 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term8 A s t).
Proof. exact (MK_COMB (@lem3236103 A s) (@lem3236109 A t)). Qed.
Lemma lem3236121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (((@UNION A s t) = (@EMPTY A)) = (term7 A s t)) = ((term1 A s t) = (term8 A s t)).
Proof. exact (MK_COMB (@lem3236085 A s t) (@lem3236118 A s t)). Qed.
Lemma lem3236126 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3236121 A s t)). Qed.
Lemma lem3236127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236128 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3236127 A) (@lem3236126 A s)). Qed.
Lemma lem3236133 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3236128 A s)). Qed.
Lemma lem3236134 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236135 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem3236134 A) (@lem3236133 A)). Qed.
Lemma lem3236140 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem3236135 A)). Qed.
Lemma lem3236158 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3236159 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (@lem3236158 A s x t). Qed.
Lemma lem3236163 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3236164 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3236163 A P x). Qed.
Lemma lem3236165 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3236164 A s x). Qed.
Lemma lem3236166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236167 {A : Type'} (s : A -> Prop) (x : A) : (term19 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3236166) (@lem3236165 A s x)). Qed.
Lemma lem3236169 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3236170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3236169 A P x). Qed.
Lemma lem3236171 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3236170 A t x). Qed.
Lemma lem3236172 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term18 A s x t) = (term21 A s t x).
Proof. exact (MK_COMB (@lem3236167 A s x) (@lem3236171 A t x)). Qed.
Lemma lem3236175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A x s t) = (term21 A s t x).
Proof. exact (TRANS (@lem3236159 A s x t) (@lem3236172 A s t x)). Qed.
Lemma lem3236176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236177 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term22 A x s t) = (term23 A s t x).
Proof. exact (MK_COMB (@lem3236176) (@lem3236175 A s t x)). Qed.
Lemma lem3236179 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3236180 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3236179 A x). Qed.
Lemma lem3236181 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term17 A x s t) = (@IN A x (@EMPTY A))) = ((term21 A s t x) = False).
Proof. exact (MK_COMB (@lem3236177 A s t x) (@lem3236180 A x)). Qed.
Lemma lem3236183 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3236184 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term21 A s t x) = False) = (term24 A s t x).
Proof. exact (@lem3236183 (term21 A s t x)). Qed.
Lemma lem3236187 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term17 A x s t) = (@IN A x (@EMPTY A))) = (term24 A s t x).
Proof. exact (TRANS (@lem3236181 A s t x) (@lem3236184 A s t x)). Qed.
Lemma lem3236188 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236187 A s t x)). Qed.
Lemma lem3236189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236190 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term27 A s t).
Proof. exact (MK_COMB (@lem3236189 A) (@lem3236188 A s t)). Qed.
Lemma lem3236195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236196 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3236195) (@lem3236190 A s t)). Qed.
Lemma lem3236206 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3236207 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3236206 A P x). Qed.
Lemma lem3236208 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3236207 A s x). Qed.
Lemma lem3236209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236210 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (MK_COMB (@lem3236209) (@lem3236208 A s x)). Qed.
Lemma lem3236212 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3236213 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3236212 A x). Qed.
Lemma lem3236214 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3236210 A s x) (@lem3236213 A x)). Qed.
Lemma lem3236216 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3236217 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term31 A s x).
Proof. exact (@lem3236216 (s x)). Qed.
Lemma lem3236218 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term31 A s x).
Proof. exact (TRANS (@lem3236214 A s x) (@lem3236217 A s x)). Qed.
Lemma lem3236219 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236218 A s x)). Qed.
Lemma lem3236220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236221 {A : Type'} (s : A -> Prop) : (term4 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236220 A) (@lem3236219 A s)). Qed.
Lemma lem3236226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236227 {A : Type'} (s : A -> Prop) : (term6 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3236226) (@lem3236221 A s)). Qed.
Lemma lem3236235 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3236236 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3236235 A P x). Qed.
Lemma lem3236237 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3236236 A t x). Qed.
Lemma lem3236238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236239 {A : Type'} (t : A -> Prop) (x : A) : (term29 A x t) = (term30 A t x).
Proof. exact (MK_COMB (@lem3236238) (@lem3236237 A t x)). Qed.
Lemma lem3236241 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3236242 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3236241 A x). Qed.
Lemma lem3236243 {A : Type'} (t : A -> Prop) (x : A) : ((@IN A x t) = (@IN A x (@EMPTY A))) = ((t x) = False).
Proof. exact (MK_COMB (@lem3236239 A t x) (@lem3236242 A x)). Qed.
Lemma lem3236245 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3236246 {A : Type'} (t : A -> Prop) (x : A) : ((t x) = False) = (term31 A t x).
Proof. exact (@lem3236245 (t x)). Qed.
Lemma lem3236247 {A : Type'} (t : A -> Prop) (x : A) : ((@IN A x t) = (@IN A x (@EMPTY A))) = (term31 A t x).
Proof. exact (TRANS (@lem3236243 A t x) (@lem3236246 A t x)). Qed.
Lemma lem3236248 {A : Type'} (t : A -> Prop) : (term32 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236247 A t x)). Qed.
Lemma lem3236249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236250 {A : Type'} (t : A -> Prop) : (term4 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236249 A) (@lem3236248 A t)). Qed.
Lemma lem3236255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3236227 A s) (@lem3236250 A t)). Qed.
Lemma lem3236258 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term1 A s t) = (term8 A s t)) = ((term27 A s t) = (term36 A s t)).
Proof. exact (MK_COMB (@lem3236196 A s t) (@lem3236255 A s t)). Qed.
Lemma lem3236261 {A : Type'} (s : A -> Prop) : (term10 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3236258 A s t)). Qed.
Lemma lem3236262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236263 {A : Type'} (s : A -> Prop) : (term12 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3236262 A) (@lem3236261 A s)). Qed.
Lemma lem3236268 {A : Type'} : (term14 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3236263 A s)). Qed.
Lemma lem3236269 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236270 {A : Type'} : (term16 A) = (term40 A).
Proof. exact (MK_COMB (@lem3236269 A) (@lem3236268 A)). Qed.
Lemma lem3236275 {A : Type'} : (term40 A) = (term16 A).
Proof. exact (SYM (@lem3236270 A)). Qed.
Lemma lem3236277 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3236278 {A : Type'} : (term40 A) = (term42 A).
Proof. exact (@lem3236277 (term40 A)). Qed.
Lemma lem3236279 {A : Type'} : (term42 A) = (term40 A).
Proof. exact (SYM (@lem3236278 A)). Qed.
Lemma lem3236280 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3236283 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3236284 {A : Type'} : term44 A.
Proof. exact (fun h0 : term42 A => @lem3236283 A h0). Qed.
Lemma lem3236285 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem3236286 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3236287 {A : Type'} (h1 : term42 A) (h2 : term44 A) : term42 A.
Proof. exact (@lem3236285 A h2 (@lem3236286 A h1)). Qed.
Lemma lem3236288 {A : Type'} (h1 : term42 A) : term45 A.
Proof. exact (fun h0 : term44 A => @lem3236287 A h1 h0). Qed.
Lemma lem3236289 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem3236290 {A : Type'} (h1 : term42 A) (h2 : term44 A) : term42 A.
Proof. exact (@lem3236288 A h1 (@lem3236289 A h2)). Qed.
Lemma lem3236291 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (fun h0 : term42 A => @lem3236290 A h0 h1). Qed.
Lemma lem3236292 {A : Type'} : term46 A.
Proof. exact (fun h0 : term44 A => @lem3236291 A h0). Qed.
Lemma lem3236295 {A : Type'} : term44 A.
Proof. exact (@lem3236292 A (@lem3236284 A)). Qed.
Lemma lem3236296 {A : Type'} : term44 A.
Proof. exact (@lem3236295 A). Qed.
Lemma lem3236298 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3236299 {A : Type'} : (term42 A) = (term47 A).
Proof. exact (@lem3236298 (term43 A)). Qed.
Lemma lem3236301 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3236302 {A : Type'} : (term47 A) = (term40 A).
Proof. exact (@lem3236301 (term40 A)). Qed.
Lemma lem3236331 {A : Type'} : (term42 A) = (term40 A).
Proof. exact (TRANS (@lem3236299 A) (@lem3236302 A)). Qed.
Lemma lem3236334 {A : Type'} (t : A -> Prop) (x : A) : (term31 A t x) = (term31 A t x).
Proof. exact (eq_refl (term31 A t x)). Qed.
Lemma lem3236335 {A : Type'} (t : A -> Prop) : (term33 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236334 A t x)). Qed.
Lemma lem3236336 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236337 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236336 A) (@lem3236335 A t)). Qed.
Lemma lem3236340 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term31 A s x).
Proof. exact (eq_refl (term31 A s x)). Qed.
Lemma lem3236341 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236340 A s x)). Qed.
Lemma lem3236342 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236343 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236342 A) (@lem3236341 A s)). Qed.
Lemma lem3236344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236345 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3236344) (@lem3236343 A s)). Qed.
Lemma lem3236346 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3236345 A s) (@lem3236337 A t)). Qed.
Lemma lem3236353 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term24 A s t x) = (term24 A s t x).
Proof. exact (eq_refl (term24 A s t x)). Qed.
Lemma lem3236354 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236353 A s t x)). Qed.
Lemma lem3236355 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236356 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term27 A s t).
Proof. exact (MK_COMB (@lem3236355 A) (@lem3236354 A s t)). Qed.
Lemma lem3236357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236358 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term28 A s t).
Proof. exact (MK_COMB (@lem3236357) (@lem3236356 A s t)). Qed.
Lemma lem3236359 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term27 A s t) = (term36 A s t)) = ((term27 A s t) = (term36 A s t)).
Proof. exact (MK_COMB (@lem3236358 A s t) (@lem3236346 A s t)). Qed.
Lemma lem3236360 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3236359 A s t)). Qed.
Lemma lem3236361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236362 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3236361 A) (@lem3236360 A s)). Qed.
Lemma lem3236363 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3236362 A s)). Qed.
Lemma lem3236364 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236365 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem3236364 A) (@lem3236363 A)). Qed.
Lemma lem3236402 {A : Type'} : (term42 A) = (term40 A).
Proof. exact (TRANS (@lem3236331 A) (@lem3236365 A)). Qed.
Lemma lem3236403 {A : Type'} : (term40 A) = (term42 A).
Proof. exact (SYM (@lem3236402 A)). Qed.
Lemma lem3236405 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3236406 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term27 A s t) = (term36 A s t)) = (term49 A s t).
Proof. exact (@lem3236405 ((term27 A s t) = (term36 A s t))). Qed.
Lemma lem3236407 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = ((term27 A s t) = (term36 A s t)).
Proof. exact (SYM (@lem3236406 A s t)). Qed.
Lemma lem3236408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term50 A s t) : term50 A s t.
Proof. exact (h1). Qed.
Lemma lem3236417 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term24 A s t x) = (term51 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3236422 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term21 A s t x).
Proof. exact (@lem16933 (term21 A s t x)). Qed.
Lemma lem3236423 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3236424 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term55 A s t) = (term56 A s t).
Proof. exact (@lem3236423 A (term26 A s t)). Qed.
Lemma lem3236425 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term57 A s t x) = (term24 A s t x).
Proof. exact (eq_refl (term57 A s t x)). Qed.
Lemma lem3236426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3236427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term52 A s t x).
Proof. exact (MK_COMB (@lem3236426) (@lem3236425 A s t x)). Qed.
Lemma lem3236428 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term58 A s t x) = (term21 A s t x).
Proof. exact (TRANS (@lem3236427 A s t x) (@lem3236422 A s t x)). Qed.
Lemma lem3236429 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term60 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236428 A s t x)). Qed.
Lemma lem3236430 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236431 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term56 A s t) = (term61 A s t).
Proof. exact (MK_COMB (@lem3236430 A) (@lem3236429 A s t)). Qed.
Lemma lem3236432 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term55 A s t) = (term61 A s t).
Proof. exact (TRANS (@lem3236424 A s t) (@lem3236431 A s t)). Qed.
Lemma lem3236433 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term62 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236417 A s t x)). Qed.
Lemma lem3236434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term63 A s t).
Proof. exact (MK_COMB (@lem3236434 A) (@lem3236433 A s t)). Qed.
Lemma lem3236436 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term31 A s x).
Proof. exact (eq_refl (term31 A s x)). Qed.
Lemma lem3236439 {A : Type'} (s : A -> Prop) (x : A) : (term64 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3236440 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3236441 {A : Type'} (s : A -> Prop) : (term65 A s) = (term66 A s).
Proof. exact (@lem3236440 A (term33 A s)). Qed.
Lemma lem3236442 {A : Type'} (s : A -> Prop) (x : A) : (term67 A s x) = (term31 A s x).
Proof. exact (eq_refl (term67 A s x)). Qed.
Lemma lem3236443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3236444 {A : Type'} (s : A -> Prop) (x : A) : (term68 A s x) = (term64 A s x).
Proof. exact (MK_COMB (@lem3236443) (@lem3236442 A s x)). Qed.
Lemma lem3236445 {A : Type'} (s : A -> Prop) (x : A) : (term68 A s x) = (s x).
Proof. exact (TRANS (@lem3236444 A s x) (@lem3236439 A s x)). Qed.
Lemma lem3236446 {A : Type'} (s : A -> Prop) : (term69 A s) = (term70 A s).
Proof. exact (fun_ext (fun x : A => @lem3236445 A s x)). Qed.
Lemma lem3236447 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236448 {A : Type'} (s : A -> Prop) : (term66 A s) = (term71 A s).
Proof. exact (MK_COMB (@lem3236447 A) (@lem3236446 A s)). Qed.
Lemma lem3236449 {A : Type'} (s : A -> Prop) : (term65 A s) = (term71 A s).
Proof. exact (TRANS (@lem3236441 A s) (@lem3236448 A s)). Qed.
Lemma lem3236450 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236436 A s x)). Qed.
Lemma lem3236451 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236452 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236451 A) (@lem3236450 A s)). Qed.
Lemma lem3236453 {A : Type'} (t : A -> Prop) (x : A) : (term31 A t x) = (term31 A t x).
Proof. exact (eq_refl (term31 A t x)). Qed.
Lemma lem3236456 {A : Type'} (t : A -> Prop) (x : A) : (term64 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3236457 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3236458 {A : Type'} (t : A -> Prop) : (term65 A t) = (term66 A t).
Proof. exact (@lem3236457 A (term33 A t)). Qed.
Lemma lem3236459 {A : Type'} (t : A -> Prop) (x : A) : (term67 A t x) = (term31 A t x).
Proof. exact (eq_refl (term67 A t x)). Qed.
Lemma lem3236460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3236461 {A : Type'} (t : A -> Prop) (x : A) : (term68 A t x) = (term64 A t x).
Proof. exact (MK_COMB (@lem3236460) (@lem3236459 A t x)). Qed.
Lemma lem3236462 {A : Type'} (t : A -> Prop) (x : A) : (term68 A t x) = (t x).
Proof. exact (TRANS (@lem3236461 A t x) (@lem3236456 A t x)). Qed.
Lemma lem3236463 {A : Type'} (t : A -> Prop) : (term69 A t) = (term70 A t).
Proof. exact (fun_ext (fun x : A => @lem3236462 A t x)). Qed.
Lemma lem3236464 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236465 {A : Type'} (t : A -> Prop) : (term66 A t) = (term71 A t).
Proof. exact (MK_COMB (@lem3236464 A) (@lem3236463 A t)). Qed.
Lemma lem3236466 {A : Type'} (t : A -> Prop) : (term65 A t) = (term71 A t).
Proof. exact (TRANS (@lem3236458 A t) (@lem3236465 A t)). Qed.
Lemma lem3236467 {A : Type'} (t : A -> Prop) : (term33 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236453 A t x)). Qed.
Lemma lem3236468 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236469 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236468 A) (@lem3236467 A t)). Qed.
Lemma lem3236470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236471 {A : Type'} (s : A -> Prop) : (term72 A s) = (term73 A s).
Proof. exact (MK_COMB (@lem3236470) (@lem3236449 A s)). Qed.
Lemma lem3236472 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term74 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3236471 A s) (@lem3236466 A t)). Qed.
Lemma lem3236473 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term74 A s t).
Proof. exact (@lem17045 (term34 A s) (term34 A t)). Qed.
Lemma lem3236474 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term75 A s t).
Proof. exact (TRANS (@lem3236473 A s t) (@lem3236472 A s t)). Qed.
Lemma lem3236475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236476 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3236475) (@lem3236452 A s)). Qed.
Lemma lem3236477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3236476 A s) (@lem3236469 A t)). Qed.
Lemma lem3236478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236479 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem3236478) (@lem3236432 A s t)). Qed.
Lemma lem3236480 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term80 A s t).
Proof. exact (MK_COMB (@lem3236479 A s t) (@lem3236477 A s t)). Qed.
Lemma lem3236481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236482 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term82 A s t).
Proof. exact (MK_COMB (@lem3236481) (@lem3236435 A s t)). Qed.
Lemma lem3236483 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term84 A s t).
Proof. exact (MK_COMB (@lem3236482 A s t) (@lem3236474 A s t)). Qed.
Lemma lem3236484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3236484) (@lem3236483 A s t)). Qed.
Lemma lem3236486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term88 A s t).
Proof. exact (MK_COMB (@lem3236485 A s t) (@lem3236480 A s t)). Qed.
Lemma lem3236487 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term87 A s t).
Proof. exact (@lem17646 (term27 A s t) (term36 A s t)). Qed.
Lemma lem3236488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term88 A s t).
Proof. exact (TRANS (@lem3236487 A s t) (@lem3236486 A s t)). Qed.
Lemma lem3236490 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3236491 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term90 A P Q).
Proof. exact (@lem3236490 A P Q). Qed.
Lemma lem3236492 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term92 A s t).
Proof. exact (@lem3236491 A (term33 A s) (term33 A t)). Qed.
Lemma lem3236493 {A : Type'} (s : A -> Prop) (x : A) : (term67 A s x) = (term31 A s x).
Proof. exact (eq_refl (term67 A s x)). Qed.
Lemma lem3236494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236495 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term94 A s x).
Proof. exact (MK_COMB (@lem3236494) (@lem3236493 A s x)). Qed.
Lemma lem3236496 {A : Type'} (t : A -> Prop) (x : A) : (term67 A t x) = (term31 A t x).
Proof. exact (eq_refl (term67 A t x)). Qed.
Lemma lem3236497 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term95 A s t x) = (term51 A s t x).
Proof. exact (MK_COMB (@lem3236495 A s x) (@lem3236496 A t x)). Qed.
Lemma lem3236498 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term62 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236497 A s t x)). Qed.
Lemma lem3236499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term63 A s t).
Proof. exact (MK_COMB (@lem3236499 A) (@lem3236498 A s t)). Qed.
Lemma lem3236501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3236501) (@lem3236500 A s t)). Qed.
Lemma lem3236503 {A : Type'} (s : A -> Prop) (x : A) : (term67 A s x) = (term31 A s x).
Proof. exact (eq_refl (term67 A s x)). Qed.
Lemma lem3236504 {A : Type'} (s : A -> Prop) : (term99 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236503 A s x)). Qed.
Lemma lem3236505 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236506 {A : Type'} (s : A -> Prop) : (term100 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236505 A) (@lem3236504 A s)). Qed.
Lemma lem3236507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236508 {A : Type'} (s : A -> Prop) : (term101 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3236507) (@lem3236506 A s)). Qed.
Lemma lem3236509 {A : Type'} (t : A -> Prop) (x : A) : (term67 A t x) = (term31 A t x).
Proof. exact (eq_refl (term67 A t x)). Qed.
Lemma lem3236510 {A : Type'} (t : A -> Prop) : (term99 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236509 A t x)). Qed.
Lemma lem3236511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236512 {A : Type'} (t : A -> Prop) : (term100 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236511 A) (@lem3236510 A t)). Qed.
Lemma lem3236513 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3236508 A s) (@lem3236512 A t)). Qed.
Lemma lem3236514 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term91 A s t) = (term92 A s t)) = ((term63 A s t) = (term36 A s t)).
Proof. exact (MK_COMB (@lem3236502 A s t) (@lem3236513 A s t)). Qed.
Lemma lem3236515 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term63 A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3236514 A s t) (@lem3236492 A s t)). Qed.
Lemma lem3236524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236525 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term102 A s t).
Proof. exact (MK_COMB (@lem3236524) (@lem3236515 A s t)). Qed.
Lemma lem3236534 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term75 A s t).
Proof. exact (eq_refl (term75 A s t)). Qed.
Lemma lem3236535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3236525 A s t) (@lem3236534 A s t)). Qed.
Lemma lem3236536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236537 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term104 A s t).
Proof. exact (MK_COMB (@lem3236536) (@lem3236535 A s t)). Qed.
Lemma lem3236539 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3236540 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term75 A P Q).
Proof. exact (@lem3236539 A P Q). Qed.
Lemma lem3236541 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term75 A s t).
Proof. exact (@lem3236540 A s t). Qed.
Lemma lem3236550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3236550) (@lem3236541 A s t)). Qed.
Lemma lem3236560 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem3236561 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3236551 A s t) (@lem3236560 A s t)). Qed.
Lemma lem3236562 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term107 A s t).
Proof. exact (MK_COMB (@lem3236537 A s t) (@lem3236561 A s t)). Qed.
Lemma lem3236564 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3236565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term61 A P Q).
Proof. exact (@lem3236564 A P Q). Qed.
Lemma lem3236566 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term61 A s t).
Proof. exact (@lem3236565 A s t). Qed.
Lemma lem3236567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term102 A s t).
Proof. exact (eq_refl (term102 A s t)). Qed.
Lemma lem3236568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term103 A s t) = (term108 A s t).
Proof. exact (MK_COMB (@lem3236567 A s t) (@lem3236566 A s t)). Qed.
Lemma lem3236570 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3236571 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (@lem3236570 A P Q). Qed.
Lemma lem3236572 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term112 A s t).
Proof. exact (@lem3236571 A (term36 A s t) (term60 A s t)). Qed.
Lemma lem3236573 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term113 A s t x) = (term21 A s t x).
Proof. exact (eq_refl (term113 A s t x)). Qed.
Lemma lem3236574 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term60 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236573 A s t x)). Qed.
Lemma lem3236575 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term61 A s t).
Proof. exact (MK_COMB (@lem3236575 A) (@lem3236574 A s t)). Qed.
Lemma lem3236577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term102 A s t).
Proof. exact (eq_refl (term102 A s t)). Qed.
Lemma lem3236578 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term108 A s t).
Proof. exact (MK_COMB (@lem3236577 A s t) (@lem3236576 A s t)). Qed.
Lemma lem3236579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236580 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term117 A s t).
Proof. exact (MK_COMB (@lem3236579) (@lem3236578 A s t)). Qed.
Lemma lem3236581 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term113 A s t x) = (term21 A s t x).
Proof. exact (eq_refl (term113 A s t x)). Qed.
Lemma lem3236582 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term102 A s t).
Proof. exact (eq_refl (term102 A s t)). Qed.
Lemma lem3236583 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term118 A s t x) = (term119 A s t x).
Proof. exact (MK_COMB (@lem3236582 A s t) (@lem3236581 A s t x)). Qed.
Lemma lem3236584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A s t) = (term121 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236583 A s t x)). Qed.
Lemma lem3236585 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236586 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term122 A s t).
Proof. exact (MK_COMB (@lem3236585 A) (@lem3236584 A s t)). Qed.
Lemma lem3236587 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term111 A s t) = (term112 A s t)) = ((term108 A s t) = (term122 A s t)).
Proof. exact (MK_COMB (@lem3236580 A s t) (@lem3236586 A s t)). Qed.
Lemma lem3236588 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term122 A s t).
Proof. exact (EQ_MP (@lem3236587 A s t) (@lem3236572 A s t)). Qed.
Lemma lem3236589 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term103 A s t) = (term122 A s t).
Proof. exact (TRANS (@lem3236568 A s t) (@lem3236588 A s t)). Qed.
Lemma lem3236590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236591 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term123 A s t).
Proof. exact (MK_COMB (@lem3236590) (@lem3236589 A s t)). Qed.
Lemma lem3236593 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3236594 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term61 A P Q).
Proof. exact (@lem3236593 A P Q). Qed.
Lemma lem3236595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term61 A s t).
Proof. exact (@lem3236594 A s t). Qed.
Lemma lem3236596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236597 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem3236596) (@lem3236595 A s t)). Qed.
Lemma lem3236598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem3236599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term80 A s t).
Proof. exact (MK_COMB (@lem3236597 A s t) (@lem3236598 A s t)). Qed.
Lemma lem3236601 {A : Type'} (P : A -> Prop) (Q : Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3236602 {A : Type'} (P : A -> Prop) (Q : Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (@lem3236601 A P Q). Qed.
Lemma lem3236603 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term127 A s t).
Proof. exact (@lem3236602 A (term60 A s t) (term36 A s t)). Qed.
Lemma lem3236604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term113 A s t x) = (term21 A s t x).
Proof. exact (eq_refl (term113 A s t x)). Qed.
Lemma lem3236605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term60 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236604 A s t x)). Qed.
Lemma lem3236606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236607 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term61 A s t).
Proof. exact (MK_COMB (@lem3236606 A) (@lem3236605 A s t)). Qed.
Lemma lem3236608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236609 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term128 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem3236608) (@lem3236607 A s t)). Qed.
Lemma lem3236610 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem3236611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term80 A s t).
Proof. exact (MK_COMB (@lem3236609 A s t) (@lem3236610 A s t)). Qed.
Lemma lem3236612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term129 A s t) = (term130 A s t).
Proof. exact (MK_COMB (@lem3236612) (@lem3236611 A s t)). Qed.
Lemma lem3236614 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term113 A s t x) = (term21 A s t x).
Proof. exact (eq_refl (term113 A s t x)). Qed.
Lemma lem3236615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236616 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term131 A s t x) = (term132 A s t x).
Proof. exact (MK_COMB (@lem3236615) (@lem3236614 A s t x)). Qed.
Lemma lem3236617 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem3236618 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term133 A x s t) = (term134 A x s t).
Proof. exact (MK_COMB (@lem3236616 A s t x) (@lem3236617 A s t)). Qed.
Lemma lem3236619 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term136 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236618 A x s t)). Qed.
Lemma lem3236620 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236621 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term127 A s t) = (term137 A s t).
Proof. exact (MK_COMB (@lem3236620 A) (@lem3236619 A s t)). Qed.
Lemma lem3236622 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term126 A s t) = (term127 A s t)) = ((term80 A s t) = (term137 A s t)).
Proof. exact (MK_COMB (@lem3236613 A s t) (@lem3236621 A s t)). Qed.
Lemma lem3236623 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term137 A s t).
Proof. exact (EQ_MP (@lem3236622 A s t) (@lem3236603 A s t)). Qed.
Lemma lem3236624 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term137 A s t).
Proof. exact (TRANS (@lem3236599 A s t) (@lem3236623 A s t)). Qed.
Lemma lem3236625 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term138 A s t).
Proof. exact (MK_COMB (@lem3236591 A s t) (@lem3236624 A s t)). Qed.
Lemma lem3236627 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3236628 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term61 A P Q).
Proof. exact (@lem3236627 A P Q). Qed.
Lemma lem3236629 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term140 A s t).
Proof. exact (@lem3236628 A (term121 A s t) (term136 A s t)). Qed.
Lemma lem3236630 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term141 A s t x) = (term119 A s t x).
Proof. exact (eq_refl (term141 A s t x)). Qed.
Lemma lem3236631 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term142 A s t) = (term121 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236630 A s t x)). Qed.
Lemma lem3236632 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236633 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term122 A s t).
Proof. exact (MK_COMB (@lem3236632 A) (@lem3236631 A s t)). Qed.
Lemma lem3236634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term123 A s t).
Proof. exact (MK_COMB (@lem3236634) (@lem3236633 A s t)). Qed.
Lemma lem3236636 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term145 A s t x) = (term134 A x s t).
Proof. exact (eq_refl (term145 A s t x)). Qed.
Lemma lem3236637 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (term136 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236636 A x s t)). Qed.
Lemma lem3236638 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236639 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term137 A s t).
Proof. exact (MK_COMB (@lem3236638 A) (@lem3236637 A s t)). Qed.
Lemma lem3236640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term138 A s t).
Proof. exact (MK_COMB (@lem3236635 A s t) (@lem3236639 A s t)). Qed.
Lemma lem3236641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236642 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term148 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3236641) (@lem3236640 A s t)). Qed.
Lemma lem3236643 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term141 A s t x) = (term119 A s t x).
Proof. exact (eq_refl (term141 A s t x)). Qed.
Lemma lem3236644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236645 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term150 A s t x) = (term151 A s t x).
Proof. exact (MK_COMB (@lem3236644) (@lem3236643 A s t x)). Qed.
Lemma lem3236646 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term145 A s t x) = (term134 A x s t).
Proof. exact (eq_refl (term145 A s t x)). Qed.
Lemma lem3236647 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term152 A s t x) = (term153 A x s t).
Proof. exact (MK_COMB (@lem3236645 A s t x) (@lem3236646 A x s t)). Qed.
Lemma lem3236648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term155 A s t).
Proof. exact (fun_ext (fun x : A => @lem3236647 A x s t)). Qed.
Lemma lem3236649 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3236650 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term140 A s t) = (term156 A s t).
Proof. exact (MK_COMB (@lem3236649 A) (@lem3236648 A s t)). Qed.
Lemma lem3236651 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term139 A s t) = (term140 A s t)) = ((term138 A s t) = (term156 A s t)).
Proof. exact (MK_COMB (@lem3236642 A s t) (@lem3236650 A s t)). Qed.
Lemma lem3236652 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term156 A s t).
Proof. exact (EQ_MP (@lem3236651 A s t) (@lem3236629 A s t)). Qed.
Lemma lem3236653 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term156 A s t).
Proof. exact (TRANS (@lem3236625 A s t) (@lem3236652 A s t)). Qed.
Lemma lem3236654 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term156 A s t).
Proof. exact (TRANS (@lem3236562 A s t) (@lem3236653 A s t)). Qed.
Lemma lem3236655 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term156 A s t).
Proof. exact (TRANS (@lem3236488 A s t) (@lem3236654 A s t)). Qed.
Lemma lem3236656 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term50 A s t) : term156 A s t.
Proof. exact (EQ_MP (@lem3236655 A s t) (@lem3236408 A s t h1)). Qed.
Lemma lem3236657 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x s t) : term153 A x s t.
Proof. exact (h1). Qed.
Lemma lem3236662 {A : Type'} (t : A -> Prop) (x : A) : (term31 A t x) = (term31 A t x).
Proof. exact (eq_refl (term31 A t x)). Qed.
Lemma lem3236663 {A : Type'} (t : A -> Prop) : (term33 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236662 A t x)). Qed.
Lemma lem3236664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236665 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236664 A) (@lem3236663 A t)). Qed.
Lemma lem3236670 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term31 A s x).
Proof. exact (eq_refl (term31 A s x)). Qed.
Lemma lem3236671 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236670 A s x)). Qed.
Lemma lem3236672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236673 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236672 A) (@lem3236671 A s)). Qed.
Lemma lem3236674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236675 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3236674) (@lem3236673 A s)). Qed.
Lemma lem3236676 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3236675 A s) (@lem3236665 A t)). Qed.
Lemma lem3236687 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term132 A s t x) = (term132 A s t x).
Proof. exact (eq_refl (term132 A s t x)). Qed.
Lemma lem3236688 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term134 A x s t) = (term134 A x s t).
Proof. exact (MK_COMB (@lem3236687 A s t x) (@lem3236676 A s t)). Qed.
Lemma lem3236697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term21 A s t x) = (term21 A s t x).
Proof. exact (eq_refl (term21 A s t x)). Qed.
Lemma lem3236702 {A : Type'} (t : A -> Prop) (x : A) : (term31 A t x) = (term31 A t x).
Proof. exact (eq_refl (term31 A t x)). Qed.
Lemma lem3236703 {A : Type'} (t : A -> Prop) : (term33 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236702 A t x)). Qed.
Lemma lem3236704 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236705 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236704 A) (@lem3236703 A t)). Qed.
Lemma lem3236710 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term31 A s x).
Proof. exact (eq_refl (term31 A s x)). Qed.
Lemma lem3236711 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236710 A s x)). Qed.
Lemma lem3236712 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236713 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236712 A) (@lem3236711 A s)). Qed.
Lemma lem3236714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236715 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3236714) (@lem3236713 A s)). Qed.
Lemma lem3236716 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3236715 A s) (@lem3236705 A t)). Qed.
Lemma lem3236717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3236718 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term102 A s t).
Proof. exact (MK_COMB (@lem3236717) (@lem3236716 A s t)). Qed.
Lemma lem3236719 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term119 A s t x) = (term119 A s t x).
Proof. exact (MK_COMB (@lem3236718 A s t) (@lem3236697 A s t x)). Qed.
Lemma lem3236720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term151 A s t x) = (term151 A s t x).
Proof. exact (MK_COMB (@lem3236720) (@lem3236719 A s t x)). Qed.
Lemma lem3236722 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term153 A x s t) = (term153 A x s t).
Proof. exact (MK_COMB (@lem3236721 A s t x) (@lem3236688 A x s t)). Qed.
Lemma lem3236723 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x s t) : term153 A x s t.
Proof. exact (EQ_MP (@lem3236722 A x s t) (@lem3236657 A x s t h1)). Qed.
Lemma lem3236724 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term119 A s t x.
Proof. exact (h1). Qed.
Lemma lem3236725 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term134 A x s t.
Proof. exact (h1). Qed.
Lemma lem3236726 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term21 A s t x.
Proof. exact (proj2 (@lem3236724 A s t x h1)). Qed.
Lemma lem3236727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term36 A s t.
Proof. exact (proj1 (@lem3236724 A s t x h1)). Qed.
Lemma lem3236728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term34 A t.
Proof. exact (proj2 (@lem3236727 A s t x h1)). Qed.
Lemma lem3236729 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term34 A s.
Proof. exact (proj1 (@lem3236727 A s t x h1)). Qed.
Lemma lem3236732 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term36 A s t.
Proof. exact (proj2 (@lem3236725 A x s t h1)). Qed.
Lemma lem3236733 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term21 A s t x.
Proof. exact (proj1 (@lem3236725 A x s t h1)). Qed.
Lemma lem3236734 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term34 A t.
Proof. exact (proj2 (@lem3236732 A x s t h1)). Qed.
Lemma lem3236735 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term34 A s.
Proof. exact (proj1 (@lem3236732 A x s t h1)). Qed.
Lemma lem3236739 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term31 A s x).
Proof. exact (eq_refl (term31 A s x)). Qed.
Lemma lem3236740 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236739 A s x)). Qed.
Lemma lem3236741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236743 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236741 A) (@lem3236740 A s)). Qed.
Lemma lem3236744 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term34 A s.
Proof. exact (EQ_MP (@lem3236743 A s) (@lem3236729 A s t x h1)). Qed.
Lemma lem3236755 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3236764 {A : Type'} (t : A -> Prop) (x : A) : (term31 A t x) = (term31 A t x).
Proof. exact (eq_refl (term31 A t x)). Qed.
Lemma lem3236765 {A : Type'} (t : A -> Prop) : (term33 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236764 A t x)). Qed.
Lemma lem3236766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236768 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236766 A) (@lem3236765 A t)). Qed.
Lemma lem3236769 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term34 A t.
Proof. exact (EQ_MP (@lem3236768 A t) (@lem3236728 A s t x h1)). Qed.
Lemma lem3236773 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3236775 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term31 A s x).
Proof. exact (eq_refl (term31 A s x)). Qed.
Lemma lem3236776 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3236775 A s x)). Qed.
Lemma lem3236777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236779 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3236777 A) (@lem3236776 A s)). Qed.
Lemma lem3236780 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term34 A s.
Proof. exact (EQ_MP (@lem3236779 A s) (@lem3236735 A x s t h1)). Qed.
Lemma lem3236791 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3236800 {A : Type'} (t : A -> Prop) (x : A) : (term31 A t x) = (term31 A t x).
Proof. exact (eq_refl (term31 A t x)). Qed.
Lemma lem3236801 {A : Type'} (t : A -> Prop) : (term33 A t) = (term33 A t).
Proof. exact (fun_ext (fun x : A => @lem3236800 A t x)). Qed.
Lemma lem3236802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236804 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (MK_COMB (@lem3236802 A) (@lem3236801 A t)). Qed.
Lemma lem3236805 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term34 A t.
Proof. exact (EQ_MP (@lem3236804 A t) (@lem3236734 A x s t h1)). Qed.
Lemma lem3236809 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3236810 {A : Type'} (_33205 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term67 A s _33205.
Proof. exact (@lem3236744 A s t x h1 _33205). Qed.
Lemma lem3236811 {A : Type'} (s : A -> Prop) (_33205 : A) : (term67 A s _33205) = (term31 A s _33205).
Proof. exact (eq_refl (term67 A s _33205)). Qed.
Lemma lem3236819 {A : Type'} (_33208 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term67 A t _33208.
Proof. exact (@lem3236769 A s t x h1 _33208). Qed.
Lemma lem3236820 {A : Type'} (t : A -> Prop) (_33208 : A) : (term67 A t _33208) = (term31 A t _33208).
Proof. exact (eq_refl (term67 A t _33208)). Qed.
Lemma lem3236822 {A : Type'} (_33209 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term67 A s _33209.
Proof. exact (@lem3236780 A x s t h1 _33209). Qed.
Lemma lem3236823 {A : Type'} (s : A -> Prop) (_33209 : A) : (term67 A s _33209) = (term31 A s _33209).
Proof. exact (eq_refl (term67 A s _33209)). Qed.
Lemma lem3236831 {A : Type'} (_33212 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term67 A t _33212.
Proof. exact (@lem3236805 A x s t h1 _33212). Qed.
Lemma lem3236832 {A : Type'} (t : A -> Prop) (_33212 : A) : (term67 A t _33212) = (term31 A t _33212).
Proof. exact (eq_refl (term67 A t _33212)). Qed.
Lemma lem3236835 {A : Type'} (_33205 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term31 A s _33205.
Proof. exact (EQ_MP (@lem3236811 A s _33205) (@lem3236810 A _33205 s t x h1)). Qed.
Lemma lem3236839 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3236843 {A : Type'} (_33208 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term31 A t _33208.
Proof. exact (EQ_MP (@lem3236820 A t _33208) (@lem3236819 A _33208 s t x h1)). Qed.
Lemma lem3236845 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3236847 {A : Type'} (_33209 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term31 A s _33209.
Proof. exact (EQ_MP (@lem3236823 A s _33209) (@lem3236822 A _33209 x s t h1)). Qed.
Lemma lem3236851 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3236855 {A : Type'} (_33212 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term31 A t _33212.
Proof. exact (EQ_MP (@lem3236832 A t _33212) (@lem3236831 A _33212 x s t h1)). Qed.
Lemma lem3236857 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3236859 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3236860 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term157 A s x.
Proof. exact (fun h0 : term31 A s x => @lem3236859 A s x h1). Qed.
Lemma lem3236862 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236863 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (s x).
Proof. exact (@lem3236862 (s x)). Qed.
Lemma lem3236864 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3236863 A s x) (@lem3236860 A s x h1)). Qed.
Lemma lem3236867 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3236869 {A : Type'} (s : A -> Prop) (_33205 : A) : (term31 A s _33205) = (term159 A s _33205).
Proof. exact (@lem3236867 (s _33205)). Qed.
Lemma lem3236872 {A : Type'} (_33205 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term159 A s _33205.
Proof. exact (EQ_MP (@lem3236869 A s _33205) (@lem3236835 A _33205 s t x h1)). Qed.
Lemma lem3236873 {A : Type'} (_33205 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term159 A s _33205.
Proof. exact (@lem3236872 A _33205 s t x h1). Qed.
Lemma lem3236874 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term159 A s x.
Proof. exact (@lem3236873 A x s t x h1). Qed.
Lemma lem3236877 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : False.
Proof. exact (@lem3236874 A s t x h2 (@lem3236864 A s x h1)). Qed.
Lemma lem3236878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : term160.
Proof. exact (fun h0 : ~ False => @lem3236877 A s t x h1 h2). Qed.
Lemma lem3236880 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236881 : term160 = False.
Proof. exact (@lem3236880 False). Qed.
Lemma lem3236882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236881) (@lem3236878 A s t x h1 h2)). Qed.
Lemma lem3236884 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3236885 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term157 A t x.
Proof. exact (fun h0 : term31 A t x => @lem3236884 A t x h1). Qed.
Lemma lem3236887 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236888 {A : Type'} (t : A -> Prop) (x : A) : (term157 A t x) = (t x).
Proof. exact (@lem3236887 (t x)). Qed.
Lemma lem3236889 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3236888 A t x) (@lem3236885 A t x h1)). Qed.
Lemma lem3236892 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3236894 {A : Type'} (t : A -> Prop) (_33208 : A) : (term31 A t _33208) = (term159 A t _33208).
Proof. exact (@lem3236892 (t _33208)). Qed.
Lemma lem3236897 {A : Type'} (_33208 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term159 A t _33208.
Proof. exact (EQ_MP (@lem3236894 A t _33208) (@lem3236843 A _33208 s t x h1)). Qed.
Lemma lem3236898 {A : Type'} (_33208 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term159 A t _33208.
Proof. exact (@lem3236897 A _33208 s t x h1). Qed.
Lemma lem3236899 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : term159 A t x.
Proof. exact (@lem3236898 A x s t x h1). Qed.
Lemma lem3236902 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : False.
Proof. exact (@lem3236899 A s t x h2 (@lem3236889 A t x h1)). Qed.
Lemma lem3236903 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : term160.
Proof. exact (fun h0 : ~ False => @lem3236902 A s t x h1 h2). Qed.
Lemma lem3236905 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236906 : term160 = False.
Proof. exact (@lem3236905 False). Qed.
Lemma lem3236907 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236906) (@lem3236903 A s t x h1 h2)). Qed.
Lemma lem3236909 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3236910 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term157 A s x.
Proof. exact (fun h0 : term31 A s x => @lem3236909 A s x h1). Qed.
Lemma lem3236912 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236913 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (s x).
Proof. exact (@lem3236912 (s x)). Qed.
Lemma lem3236914 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3236913 A s x) (@lem3236910 A s x h1)). Qed.
Lemma lem3236917 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3236919 {A : Type'} (s : A -> Prop) (_33209 : A) : (term31 A s _33209) = (term159 A s _33209).
Proof. exact (@lem3236917 (s _33209)). Qed.
Lemma lem3236922 {A : Type'} (_33209 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term159 A s _33209.
Proof. exact (EQ_MP (@lem3236919 A s _33209) (@lem3236847 A _33209 x s t h1)). Qed.
Lemma lem3236923 {A : Type'} (_33209 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term159 A s _33209.
Proof. exact (@lem3236922 A _33209 x s t h1). Qed.
Lemma lem3236924 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term159 A s x.
Proof. exact (@lem3236923 A x x s t h1). Qed.
Lemma lem3236927 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : False.
Proof. exact (@lem3236924 A x s t h2 (@lem3236914 A s x h1)). Qed.
Lemma lem3236928 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : term160.
Proof. exact (fun h0 : ~ False => @lem3236927 A x s t h1 h2). Qed.
Lemma lem3236930 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236931 : term160 = False.
Proof. exact (@lem3236930 False). Qed.
Lemma lem3236932 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236931) (@lem3236928 A x s t h1 h2)). Qed.
Lemma lem3236934 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3236935 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term157 A t x.
Proof. exact (fun h0 : term31 A t x => @lem3236934 A t x h1). Qed.
Lemma lem3236937 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236938 {A : Type'} (t : A -> Prop) (x : A) : (term157 A t x) = (t x).
Proof. exact (@lem3236937 (t x)). Qed.
Lemma lem3236939 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3236938 A t x) (@lem3236935 A t x h1)). Qed.
Lemma lem3236942 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3236944 {A : Type'} (t : A -> Prop) (_33212 : A) : (term31 A t _33212) = (term159 A t _33212).
Proof. exact (@lem3236942 (t _33212)). Qed.
Lemma lem3236947 {A : Type'} (_33212 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term159 A t _33212.
Proof. exact (EQ_MP (@lem3236944 A t _33212) (@lem3236855 A _33212 x s t h1)). Qed.
Lemma lem3236948 {A : Type'} (_33212 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term159 A t _33212.
Proof. exact (@lem3236947 A _33212 x s t h1). Qed.
Lemma lem3236949 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : term159 A t x.
Proof. exact (@lem3236948 A x x s t h1). Qed.
Lemma lem3236952 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : False.
Proof. exact (@lem3236949 A x s t h2 (@lem3236939 A t x h1)). Qed.
Lemma lem3236953 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : term160.
Proof. exact (fun h0 : ~ False => @lem3236952 A x s t h1 h2). Qed.
Lemma lem3236955 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3236956 : term160 = False.
Proof. exact (@lem3236955 False). Qed.
Lemma lem3236957 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236956) (@lem3236953 A x s t h1 h2)). Qed.
Lemma lem3236958 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3236957 A x s t h1 h2) (fun h3 : False => @lem3236857 A t x h1)). Qed.
Lemma lem3236959 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236958 A x s t h1 h2) (@lem3236857 A t x h1)). Qed.
Lemma lem3236960 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3236932 A x s t h1 h2) (fun h3 : False => @lem3236851 A s x h1)). Qed.
Lemma lem3236961 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236960 A x s t h1 h2) (@lem3236851 A s x h1)). Qed.
Lemma lem3236962 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3236907 A s t x h1 h2) (fun h3 : False => @lem3236845 A t x h1)). Qed.
Lemma lem3236963 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236962 A s t x h1 h2) (@lem3236845 A t x h1)). Qed.
Lemma lem3236964 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3236882 A s t x h1 h2) (fun h3 : False => @lem3236839 A s x h1)). Qed.
Lemma lem3236965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236964 A s t x h1 h2) (@lem3236839 A s x h1)). Qed.
Lemma lem3236966 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3236959 A x s t h1 h2) (fun h3 : False => @lem3236809 A t x h1)). Qed.
Lemma lem3236967 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236966 A x s t h1 h2) (@lem3236809 A t x h1)). Qed.
Lemma lem3236968 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3236961 A x s t h1 h2) (fun h3 : False => @lem3236791 A s x h1)). Qed.
Lemma lem3236969 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236968 A x s t h1 h2) (@lem3236791 A s x h1)). Qed.
Lemma lem3236970 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3236963 A s t x h1 h2) (fun h3 : False => @lem3236773 A t x h1)). Qed.
Lemma lem3236971 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236970 A s t x h1 h2) (@lem3236773 A t x h1)). Qed.
Lemma lem3236972 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3236965 A s t x h1 h2) (fun h3 : False => @lem3236755 A s x h1)). Qed.
Lemma lem3236973 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236972 A s t x h1 h2) (@lem3236755 A s x h1)). Qed.
Lemma lem3236974 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3236967 A x s t h1 h2) (fun h3 : False => @lem3236809 A t x h1)). Qed.
Lemma lem3236975 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : t x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236974 A x s t h1 h2) (@lem3236809 A t x h1)). Qed.
Lemma lem3236976 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3236969 A x s t h1 h2) (fun h3 : False => @lem3236791 A s x h1)). Qed.
Lemma lem3236977 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x) (h2 : term134 A x s t) : False.
Proof. exact (EQ_MP (@lem3236976 A x s t h1 h2) (@lem3236791 A s x h1)). Qed.
Lemma lem3236978 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3236971 A s t x h1 h2) (fun h3 : False => @lem3236773 A t x h1)). Qed.
Lemma lem3236979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236978 A s t x h1 h2) (@lem3236773 A t x h1)). Qed.
Lemma lem3236980 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3236973 A s t x h1 h2) (fun h3 : False => @lem3236755 A s x h1)). Qed.
Lemma lem3236981 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term119 A s t x) : False.
Proof. exact (EQ_MP (@lem3236980 A s t x h1 h2) (@lem3236755 A s x h1)). Qed.
Lemma lem3236982 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term134 A x s t) : False.
Proof. exact (or_elim (@lem3236733 A x s t h1) (fun h0 : s x => @lem3236977 A x s t h0 h1) (fun h0 : t x => @lem3236975 A x s t h0 h1)). Qed.
Lemma lem3236983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term119 A s t x) : False.
Proof. exact (or_elim (@lem3236726 A s t x h1) (fun h0 : s x => @lem3236981 A s t x h0 h1) (fun h0 : t x => @lem3236979 A s t x h0 h1)). Qed.
Lemma lem3236984 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x s t) : False.
Proof. exact (or_elim (@lem3236723 A x s t h1) (fun h0 : term119 A s t x => @lem3236983 A s t x h0) (fun h0 : term134 A x s t => @lem3236982 A x s t h0)). Qed.
Lemma lem3236985 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x s t) : (term153 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term153 A x s t => @lem3236984 A x s t h1) (fun h2 : False => @lem3236723 A x s t h1)). Qed.
Lemma lem3236986 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x s t) : False.
Proof. exact (EQ_MP (@lem3236985 A x s t h1) (@lem3236723 A x s t h1)). Qed.
Lemma lem3236987 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term50 A s t) : False.
Proof. exact (ex_elim (@lem3236656 A s t h1) (fun x : A => fun h0 : term155 A s t x => @lem3236986 A x s t h0)). Qed.
Lemma lem3236988 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term50 A s t) : (term50 A s t) = False.
Proof. exact (prop_ext (fun h2 : term50 A s t => @lem3236987 A s t h1) (fun h2 : False => @lem3236408 A s t h1)). Qed.
Lemma lem3236989 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term50 A s t) : False.
Proof. exact (EQ_MP (@lem3236988 A s t h1) (@lem3236408 A s t h1)). Qed.
Lemma lem3236990 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term49 A s t.
Proof. exact (fun h0 : term50 A s t => @lem3236989 A s t h0). Qed.
Lemma lem3236991 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3236407 A s t) (@lem3236990 A s t)). Qed.
Lemma lem3236996 {A : Type'} (s : A -> Prop) : term38 A s.
Proof. exact (fun t : A -> Prop => @lem3236991 A s t). Qed.
Lemma lem3237001 {A : Type'} : term40 A.
Proof. exact (fun s : A -> Prop => @lem3236996 A s). Qed.
Lemma lem3237002 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem3236403 A) (@lem3237001 A)). Qed.
Lemma lem3237004 {A : Type'} : term42 A.
Proof. exact (@lem3236296 A (@lem3237002 A)). Qed.
Lemma lem3237005 {A : Type'} (h1 : term43 A) : False.
Proof. exact (@lem3237004 A (@lem3236280 A h1)). Qed.
Lemma lem3237006 {A : Type'} (h1 : term43 A) : (term43 A) = False.
Proof. exact (prop_ext (fun h2 : term43 A => @lem3237005 A h1) (fun h2 : False => @lem3236280 A h1)). Qed.
Lemma lem3237007 {A : Type'} (h1 : term43 A) : False.
Proof. exact (EQ_MP (@lem3237006 A h1) (@lem3236280 A h1)). Qed.
Lemma lem3237008 {A : Type'} : term42 A.
Proof. exact (fun h0 : term43 A => @lem3237007 A h0). Qed.
Lemma lem3237009 {A : Type'} : term40 A.
Proof. exact (EQ_MP (@lem3236279 A) (@lem3237008 A)). Qed.
Lemma lem3237010 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem3236275 A) (@lem3237009 A)). Qed.
Lemma lem3237011 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3236140 A) (@lem3237010 A)). Qed.
