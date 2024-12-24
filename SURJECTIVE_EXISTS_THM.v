Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_EXISTS_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Lemma lem3585087 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3585088 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (@lem3585087 (term1 A B f)). Qed.
Lemma lem3585089 {A B : Type'} (f : A -> B) : (term2 A B f) = (term1 A B f).
Proof. exact (SYM (@lem3585088 A B f)). Qed.
Lemma lem3585090 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : term3 A B f.
Proof. exact (h1). Qed.
Lemma lem3585093 {A B : Type'} (f : A -> B) (h1 : term2 A B f) : term2 A B f.
Proof. exact (h1). Qed.
Lemma lem3585094 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (fun h0 : term2 A B f => @lem3585093 A B f h0). Qed.
Lemma lem3585095 {A B : Type'} (f : A -> B) (h1 : term4 A B f) : term4 A B f.
Proof. exact (h1). Qed.
Lemma lem3585096 {A B : Type'} (f : A -> B) (h1 : term2 A B f) : term2 A B f.
Proof. exact (h1). Qed.
Lemma lem3585097 {A B : Type'} (f : A -> B) (h1 : term2 A B f) (h2 : term4 A B f) : term2 A B f.
Proof. exact (@lem3585095 A B f h2 (@lem3585096 A B f h1)). Qed.
Lemma lem3585098 {A B : Type'} (f : A -> B) (h1 : term2 A B f) : term5 A B f.
Proof. exact (fun h0 : term4 A B f => @lem3585097 A B f h1 h0). Qed.
Lemma lem3585099 {A B : Type'} (f : A -> B) (h1 : term4 A B f) : term4 A B f.
Proof. exact (h1). Qed.
Lemma lem3585100 {A B : Type'} (f : A -> B) (h1 : term2 A B f) (h2 : term4 A B f) : term2 A B f.
Proof. exact (@lem3585098 A B f h1 (@lem3585099 A B f h2)). Qed.
Lemma lem3585101 {A B : Type'} (f : A -> B) (h1 : term4 A B f) : term4 A B f.
Proof. exact (fun h0 : term2 A B f => @lem3585100 A B f h0 h1). Qed.
Lemma lem3585102 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (fun h0 : term4 A B f => @lem3585101 A B f h0). Qed.
Lemma lem3585105 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem3585102 A B f (@lem3585094 A B f)). Qed.
Lemma lem3585106 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem3585105 A B f). Qed.
Lemma lem3585112 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3585113 {A B : Type'} (f : A -> B) : (term2 A B f) = (term7 A B f).
Proof. exact (@lem3585112 (term3 A B f)). Qed.
Lemma lem3585115 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3585116 {A B : Type'} (f : A -> B) : (term7 A B f) = (term1 A B f).
Proof. exact (@lem3585115 (term1 A B f)). Qed.
Lemma lem3585119 {A B : Type'} (f : A -> B) : (term2 A B f) = (term1 A B f).
Proof. exact (TRANS (@lem3585113 A B f) (@lem3585116 A B f)). Qed.
Lemma lem3585140 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3585119 A B f)). Qed.
Lemma lem3585141 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3585150 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem3585141 A B) (@lem3585140 A B)). Qed.
Lemma lem3585151 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3585152 {B : Type'} (P : B -> Prop) : (term13 B P) = (term13 B P).
Proof. exact (fun_ext (fun y : B => @lem3585151 B P y)). Qed.
Lemma lem3585153 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3585154 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (MK_COMB (@lem3585153 B) (@lem3585152 B P)). Qed.
Lemma lem3585155 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term15 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term15 A B P f x)). Qed.
Lemma lem3585156 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term16 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3585155 A B P f x)). Qed.
Lemma lem3585157 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585158 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term17 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3585157 A) (@lem3585156 A B P f)). Qed.
Lemma lem3585159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585160 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term18 A B P f) = (term18 A B P f).
Proof. exact (MK_COMB (@lem3585159) (@lem3585158 A B P f)). Qed.
Lemma lem3585161 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term17 A B P f) = (term14 B P)) = ((term17 A B P f) = (term14 B P)).
Proof. exact (MK_COMB (@lem3585160 A B P f) (@lem3585154 B P)). Qed.
Lemma lem3585162 {A B : Type'} (f : A -> B) : (term19 A B f) = (term19 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem3585161 A B f P)). Qed.
Lemma lem3585163 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3585164 {A B : Type'} (f : A -> B) : (term20 A B f) = (term20 A B f).
Proof. exact (MK_COMB (@lem3585163 B) (@lem3585162 A B f)). Qed.
Lemma lem3585165 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3585166 {A B : Type'} (f : A -> B) (y : B) : (term21 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3585165 A B f x y)). Qed.
Lemma lem3585167 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585168 {A B : Type'} (f : A -> B) (y : B) : (term22 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3585167 A) (@lem3585166 A B f y)). Qed.
Lemma lem3585169 {A B : Type'} (f : A -> B) : (term23 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3585168 A B f y)). Qed.
Lemma lem3585170 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585171 {A B : Type'} (f : A -> B) : (term24 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3585170 B) (@lem3585169 A B f)). Qed.
Lemma lem3585172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3585173 {A B : Type'} (f : A -> B) : (term25 A B f) = (term25 A B f).
Proof. exact (MK_COMB (@lem3585172) (@lem3585171 A B f)). Qed.
Lemma lem3585174 {A B : Type'} (f : A -> B) : (term1 A B f) = (term1 A B f).
Proof. exact (MK_COMB (@lem3585173 A B f) (@lem3585164 A B f)). Qed.
Lemma lem3585175 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3585174 A B f)). Qed.
Lemma lem3585176 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3585177 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem3585176 A B) (@lem3585175 A B)). Qed.
Lemma lem3585218 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (TRANS (@lem3585150 A B) (@lem3585177 A B)). Qed.
Lemma lem3585219 {A B : Type'} : (term12 A B) = (term11 A B).
Proof. exact (SYM (@lem3585218 A B)). Qed.
Lemma lem3585220 {A B : Type'} (f : A -> B) (h1 : term24 A B f) : term24 A B f.
Proof. exact (h1). Qed.
Lemma lem3585222 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3585223 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term17 A B P f) = (term14 B P)) = (term26 A B f P).
Proof. exact (@lem3585222 ((term17 A B P f) = (term14 B P))). Qed.
Lemma lem3585224 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term26 A B f P) = ((term17 A B P f) = (term14 B P)).
Proof. exact (SYM (@lem3585223 A B f P)). Qed.
Lemma lem3585225 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term27 A B f P) : term27 A B f P.
Proof. exact (h1). Qed.
Lemma lem3585226 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3585227 {A B : Type'} (f : A -> B) (y : B) : (term21 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3585226 A B f x y)). Qed.
Lemma lem3585228 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585229 {A B : Type'} (f : A -> B) (y : B) : (term22 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3585228 A) (@lem3585227 A B f y)). Qed.
Lemma lem3585230 {A B : Type'} (f : A -> B) : (term23 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3585229 A B f y)). Qed.
Lemma lem3585231 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585232 {A B : Type'} (f : A -> B) : (term24 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3585231 B) (@lem3585230 A B f)). Qed.
Lemma lem3585243 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3585244 {A B : Type'} (P : type1470 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (@lem3585243 B A P). Qed.
Lemma lem3585245 {A B : Type'} (f : A -> B) : (term32 A B f) = (term33 A B f).
Proof. exact (@lem3585244 A B (term34 A B f)). Qed.
Lemma lem3585246 {A B : Type'} (f : A -> B) (y : B) : (term35 A B f y) = (term21 A B f y).
Proof. exact (eq_refl (term35 A B f y)). Qed.
Lemma lem3585247 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3585248 {A B : Type'} (f : A -> B) (y : B) (x : A) : (term36 A B f y x) = (term37 A B f y x).
Proof. exact (MK_COMB (@lem3585246 A B f y) (@lem3585247 A x)). Qed.
Lemma lem3585249 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term37 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term37 A B f y x)). Qed.
Lemma lem3585250 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term36 A B f y x) = ((f x) = y).
Proof. exact (TRANS (@lem3585248 A B f y x) (@lem3585249 A B f x y)). Qed.
Lemma lem3585251 {A B : Type'} (f : A -> B) (y : B) : (term38 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3585250 A B f x y)). Qed.
Lemma lem3585252 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585253 {A B : Type'} (f : A -> B) (y : B) : (term39 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3585252 A) (@lem3585251 A B f y)). Qed.
Lemma lem3585254 {A B : Type'} (f : A -> B) : (term40 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3585253 A B f y)). Qed.
Lemma lem3585255 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585256 {A B : Type'} (f : A -> B) : (term32 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3585255 B) (@lem3585254 A B f)). Qed.
Lemma lem3585257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585258 {A B : Type'} (f : A -> B) : (term41 A B f) = (term42 A B f).
Proof. exact (MK_COMB (@lem3585257) (@lem3585256 A B f)). Qed.
Lemma lem3585259 {A B : Type'} (f : A -> B) (y : B) : (term35 A B f y) = (term21 A B f y).
Proof. exact (eq_refl (term35 A B f y)). Qed.
Lemma lem3585260 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3585261 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term43 A B f x y) = (term44 A B f x y).
Proof. exact (MK_COMB (@lem3585259 A B f y) (@lem3585260 A B x y)). Qed.
Lemma lem3585262 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term44 A B f x y) = ((term45 A B f x y) = y).
Proof. exact (eq_refl (term44 A B f x y)). Qed.
Lemma lem3585263 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term43 A B f x y) = ((term45 A B f x y) = y).
Proof. exact (TRANS (@lem3585261 A B f x y) (@lem3585262 A B f x y)). Qed.
Lemma lem3585264 {A B : Type'} (f : A -> B) (x : B -> A) : (term46 A B f x) = (term47 A B f x).
Proof. exact (fun_ext (fun y : B => @lem3585263 A B f x y)). Qed.
Lemma lem3585265 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585266 {A B : Type'} (f : A -> B) (x : B -> A) : (term48 A B f x) = (term49 A B f x).
Proof. exact (MK_COMB (@lem3585265 B) (@lem3585264 A B f x)). Qed.
Lemma lem3585267 {A B : Type'} (f : A -> B) : (term50 A B f) = (term51 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem3585266 A B f x)). Qed.
Lemma lem3585268 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3585269 {A B : Type'} (f : A -> B) : (term33 A B f) = (term52 A B f).
Proof. exact (MK_COMB (@lem3585268 A B) (@lem3585267 A B f)). Qed.
Lemma lem3585270 {A B : Type'} (f : A -> B) : ((term32 A B f) = (term33 A B f)) = ((term24 A B f) = (term52 A B f)).
Proof. exact (MK_COMB (@lem3585258 A B f) (@lem3585269 A B f)). Qed.
Lemma lem3585272 {A B : Type'} (f : A -> B) : (term24 A B f) = (term52 A B f).
Proof. exact (EQ_MP (@lem3585270 A B f) (@lem3585245 A B f)). Qed.
Lemma lem3585273 {A B : Type'} (f : A -> B) : (term24 A B f) = (term52 A B f).
Proof. exact (TRANS (@lem3585232 A B f) (@lem3585272 A B f)). Qed.
Lemma lem3585274 {A B : Type'} (f : A -> B) (h1 : term24 A B f) : term52 A B f.
Proof. exact (EQ_MP (@lem3585273 A B f) (@lem3585220 A B f h1)). Qed.
Lemma lem3585276 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term15 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term15 A B P f x)). Qed.
Lemma lem3585277 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3585278 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term55 A B P f) = (term56 A B P f).
Proof. exact (@lem3585277 A (term16 A B P f)). Qed.
Lemma lem3585279 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term57 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term57 A B P f x)). Qed.
Lemma lem3585280 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3585282 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term58 A B P f x) = (term59 A B P f x).
Proof. exact (MK_COMB (@lem3585280) (@lem3585279 A B P f x)). Qed.
Lemma lem3585283 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term60 A B P f) = (term61 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3585282 A B P f x)). Qed.
Lemma lem3585284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3585285 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term56 A B P f) = (term62 A B P f).
Proof. exact (MK_COMB (@lem3585284 A) (@lem3585283 A B P f)). Qed.
Lemma lem3585286 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term55 A B P f) = (term62 A B P f).
Proof. exact (TRANS (@lem3585278 A B P f) (@lem3585285 A B P f)). Qed.
Lemma lem3585287 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term16 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3585276 A B P f x)). Qed.
Lemma lem3585288 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585289 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term17 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3585288 A) (@lem3585287 A B P f)). Qed.
Lemma lem3585291 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3585292 {B : Type'} (P : B -> Prop) : (term53 B P) = (term54 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3585293 {B : Type'} (P : B -> Prop) : (term63 B P) = (term64 B P).
Proof. exact (@lem3585292 B (term13 B P)). Qed.
Lemma lem3585294 {B : Type'} (P : B -> Prop) (y : B) : (term65 B P y) = (P y).
Proof. exact (eq_refl (term65 B P y)). Qed.
Lemma lem3585295 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3585297 {B : Type'} (P : B -> Prop) (y : B) : (term66 B P y) = (term67 B P y).
Proof. exact (MK_COMB (@lem3585295) (@lem3585294 B P y)). Qed.
Lemma lem3585298 {B : Type'} (P : B -> Prop) : (term68 B P) = (term69 B P).
Proof. exact (fun_ext (fun y : B => @lem3585297 B P y)). Qed.
Lemma lem3585299 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585300 {B : Type'} (P : B -> Prop) : (term64 B P) = (term54 B P).
Proof. exact (MK_COMB (@lem3585299 B) (@lem3585298 B P)). Qed.
Lemma lem3585301 {B : Type'} (P : B -> Prop) : (term63 B P) = (term54 B P).
Proof. exact (TRANS (@lem3585293 B P) (@lem3585300 B P)). Qed.
Lemma lem3585302 {B : Type'} (P : B -> Prop) : (term13 B P) = (term13 B P).
Proof. exact (fun_ext (fun y : B => @lem3585291 B P y)). Qed.
Lemma lem3585303 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3585304 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (MK_COMB (@lem3585303 B) (@lem3585302 B P)). Qed.
Lemma lem3585305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585306 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term70 A B P f) = (term71 A B P f).
Proof. exact (MK_COMB (@lem3585305) (@lem3585286 A B P f)). Qed.
Lemma lem3585307 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term72 A B f P) = (term73 A B f P).
Proof. exact (MK_COMB (@lem3585306 A B P f) (@lem3585304 B P)). Qed.
Lemma lem3585308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585309 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term74 A B P f) = (term74 A B P f).
Proof. exact (MK_COMB (@lem3585308) (@lem3585289 A B P f)). Qed.
Lemma lem3585310 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term75 A B f P) = (term76 A B f P).
Proof. exact (MK_COMB (@lem3585309 A B P f) (@lem3585301 B P)). Qed.
Lemma lem3585311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3585312 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term77 A B f P) = (term78 A B f P).
Proof. exact (MK_COMB (@lem3585311) (@lem3585310 A B f P)). Qed.
Lemma lem3585313 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term79 A B f P) = (term80 A B f P).
Proof. exact (MK_COMB (@lem3585312 A B f P) (@lem3585307 A B f P)). Qed.
Lemma lem3585314 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term27 A B f P) = (term79 A B f P).
Proof. exact (@lem17646 (term17 A B P f) (term14 B P)). Qed.
Lemma lem3585315 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term27 A B f P) = (term80 A B f P).
Proof. exact (TRANS (@lem3585314 A B f P) (@lem3585313 A B f P)). Qed.
Lemma lem3585334 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3585335 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (@lem3585334 A P Q). Qed.
Lemma lem3585336 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term83 A B f P) = (term84 A B f P).
Proof. exact (@lem3585335 A (term16 A B P f) (term54 B P)). Qed.
Lemma lem3585337 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term57 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term57 A B P f x)). Qed.
Lemma lem3585338 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term85 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3585337 A B P f x)). Qed.
Lemma lem3585339 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585340 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term86 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3585339 A) (@lem3585338 A B P f)). Qed.
Lemma lem3585341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585342 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term87 A B P f) = (term74 A B P f).
Proof. exact (MK_COMB (@lem3585341) (@lem3585340 A B P f)). Qed.
Lemma lem3585343 {B : Type'} (P : B -> Prop) : (term54 B P) = (term54 B P).
Proof. exact (eq_refl (term54 B P)). Qed.
Lemma lem3585344 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term83 A B f P) = (term76 A B f P).
Proof. exact (MK_COMB (@lem3585342 A B P f) (@lem3585343 B P)). Qed.
Lemma lem3585345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585346 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term88 A B f P) = (term89 A B f P).
Proof. exact (MK_COMB (@lem3585345) (@lem3585344 A B f P)). Qed.
Lemma lem3585347 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term57 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term57 A B P f x)). Qed.
Lemma lem3585348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585349 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term90 A B P f x) = (term91 A B P f x).
Proof. exact (MK_COMB (@lem3585348) (@lem3585347 A B P f x)). Qed.
Lemma lem3585350 {B : Type'} (P : B -> Prop) : (term54 B P) = (term54 B P).
Proof. exact (eq_refl (term54 B P)). Qed.
Lemma lem3585351 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term92 A B f x P) = (term93 A B f x P).
Proof. exact (MK_COMB (@lem3585349 A B P f x) (@lem3585350 B P)). Qed.
Lemma lem3585352 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term94 A B f P) = (term95 A B f P).
Proof. exact (fun_ext (fun x : A => @lem3585351 A B f x P)). Qed.
Lemma lem3585353 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585354 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term84 A B f P) = (term96 A B f P).
Proof. exact (MK_COMB (@lem3585353 A) (@lem3585352 A B f P)). Qed.
Lemma lem3585355 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term83 A B f P) = (term84 A B f P)) = ((term76 A B f P) = (term96 A B f P)).
Proof. exact (MK_COMB (@lem3585346 A B f P) (@lem3585354 A B f P)). Qed.
Lemma lem3585356 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term76 A B f P) = (term96 A B f P).
Proof. exact (EQ_MP (@lem3585355 A B f P) (@lem3585336 A B f P)). Qed.
Lemma lem3585357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3585358 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term78 A B f P) = (term97 A B f P).
Proof. exact (MK_COMB (@lem3585357) (@lem3585356 A B f P)). Qed.
Lemma lem3585360 {A : Type'} (P : Prop) (Q : A -> Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3585361 {B : Type'} (P : Prop) (Q : B -> Prop) : (term98 B P Q) = (term99 B P Q).
Proof. exact (@lem3585360 B P Q). Qed.
Lemma lem3585362 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term73 A B f P) = (term100 A B f P).
Proof. exact (@lem3585361 B (term62 A B P f) P). Qed.
Lemma lem3585363 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term80 A B f P) = (term101 A B f P).
Proof. exact (MK_COMB (@lem3585358 A B f P) (@lem3585362 A B f P)). Qed.
Lemma lem3585367 {A : Type'} (P : A -> Prop) (Q : Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3585368 {A : Type'} (P : A -> Prop) (Q : Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (@lem3585367 A P Q). Qed.
Lemma lem3585369 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term104 A B f P) = (term105 A B f P).
Proof. exact (@lem3585368 A (term95 A B f P) (term100 A B f P)). Qed.
Lemma lem3585370 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term106 A B f P x) = (term93 A B f x P).
Proof. exact (eq_refl (term106 A B f P x)). Qed.
Lemma lem3585371 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term107 A B f P) = (term95 A B f P).
Proof. exact (fun_ext (fun x : A => @lem3585370 A B f x P)). Qed.
Lemma lem3585372 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585373 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term108 A B f P) = (term96 A B f P).
Proof. exact (MK_COMB (@lem3585372 A) (@lem3585371 A B f P)). Qed.
Lemma lem3585374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3585375 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term109 A B f P) = (term97 A B f P).
Proof. exact (MK_COMB (@lem3585374) (@lem3585373 A B f P)). Qed.
Lemma lem3585376 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term100 A B f P) = (term100 A B f P).
Proof. exact (eq_refl (term100 A B f P)). Qed.
Lemma lem3585377 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term104 A B f P) = (term101 A B f P).
Proof. exact (MK_COMB (@lem3585375 A B f P) (@lem3585376 A B f P)). Qed.
Lemma lem3585378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585379 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term110 A B f P) = (term111 A B f P).
Proof. exact (MK_COMB (@lem3585378) (@lem3585377 A B f P)). Qed.
Lemma lem3585380 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term106 A B f P x) = (term93 A B f x P).
Proof. exact (eq_refl (term106 A B f P x)). Qed.
Lemma lem3585381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3585382 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term112 A B f P x) = (term113 A B f x P).
Proof. exact (MK_COMB (@lem3585381) (@lem3585380 A B f x P)). Qed.
Lemma lem3585383 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term100 A B f P) = (term100 A B f P).
Proof. exact (eq_refl (term100 A B f P)). Qed.
Lemma lem3585384 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term114 A B x f P) = (term115 A B x f P).
Proof. exact (MK_COMB (@lem3585382 A B f x P) (@lem3585383 A B f P)). Qed.
Lemma lem3585385 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term116 A B f P) = (term117 A B f P).
Proof. exact (fun_ext (fun x : A => @lem3585384 A B x f P)). Qed.
Lemma lem3585386 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585387 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term105 A B f P) = (term118 A B f P).
Proof. exact (MK_COMB (@lem3585386 A) (@lem3585385 A B f P)). Qed.
Lemma lem3585388 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term104 A B f P) = (term105 A B f P)) = ((term101 A B f P) = (term118 A B f P)).
Proof. exact (MK_COMB (@lem3585379 A B f P) (@lem3585387 A B f P)). Qed.
Lemma lem3585389 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term101 A B f P) = (term118 A B f P).
Proof. exact (EQ_MP (@lem3585388 A B f P) (@lem3585369 A B f P)). Qed.
Lemma lem3585391 {A : Type'} (P : Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3585392 {B : Type'} (P : Prop) (Q : B -> Prop) : (term119 B P Q) = (term120 B P Q).
Proof. exact (@lem3585391 B P Q). Qed.
Lemma lem3585393 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term121 A B x f P) = (term122 A B x f P).
Proof. exact (@lem3585392 B (term93 A B f x P) (term123 A B f P)). Qed.
Lemma lem3585394 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term124 A B f P y) = (term125 A B f P y).
Proof. exact (eq_refl (term124 A B f P y)). Qed.
Lemma lem3585395 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term126 A B f P) = (term123 A B f P).
Proof. exact (fun_ext (fun y : B => @lem3585394 A B f P y)). Qed.
Lemma lem3585396 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3585397 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term127 A B f P) = (term100 A B f P).
Proof. exact (MK_COMB (@lem3585396 B) (@lem3585395 A B f P)). Qed.
Lemma lem3585398 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term113 A B f x P) = (term113 A B f x P).
Proof. exact (eq_refl (term113 A B f x P)). Qed.
Lemma lem3585399 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term121 A B x f P) = (term115 A B x f P).
Proof. exact (MK_COMB (@lem3585398 A B f x P) (@lem3585397 A B f P)). Qed.
Lemma lem3585400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585401 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term128 A B x f P) = (term129 A B x f P).
Proof. exact (MK_COMB (@lem3585400) (@lem3585399 A B x f P)). Qed.
Lemma lem3585402 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term124 A B f P y) = (term125 A B f P y).
Proof. exact (eq_refl (term124 A B f P y)). Qed.
Lemma lem3585403 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term113 A B f x P) = (term113 A B f x P).
Proof. exact (eq_refl (term113 A B f x P)). Qed.
Lemma lem3585404 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (y : B) : (term130 A B x f P y) = (term131 A B x f P y).
Proof. exact (MK_COMB (@lem3585403 A B f x P) (@lem3585402 A B f P y)). Qed.
Lemma lem3585405 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term132 A B x f P) = (term133 A B x f P).
Proof. exact (fun_ext (fun y : B => @lem3585404 A B x f P y)). Qed.
Lemma lem3585406 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3585407 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term122 A B x f P) = (term134 A B x f P).
Proof. exact (MK_COMB (@lem3585406 B) (@lem3585405 A B x f P)). Qed.
Lemma lem3585408 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : ((term121 A B x f P) = (term122 A B x f P)) = ((term115 A B x f P) = (term134 A B x f P)).
Proof. exact (MK_COMB (@lem3585401 A B x f P) (@lem3585407 A B x f P)). Qed.
Lemma lem3585409 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) : (term115 A B x f P) = (term134 A B x f P).
Proof. exact (EQ_MP (@lem3585408 A B x f P) (@lem3585393 A B x f P)). Qed.
Lemma lem3585410 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term117 A B f P) = (term135 A B f P).
Proof. exact (fun_ext (fun x : A => @lem3585409 A B x f P)). Qed.
Lemma lem3585411 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3585412 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term118 A B f P) = (term136 A B f P).
Proof. exact (MK_COMB (@lem3585411 A) (@lem3585410 A B f P)). Qed.
Lemma lem3585413 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term101 A B f P) = (term136 A B f P).
Proof. exact (TRANS (@lem3585389 A B f P) (@lem3585412 A B f P)). Qed.
Lemma lem3585415 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term80 A B f P) = (term136 A B f P).
Proof. exact (TRANS (@lem3585363 A B f P) (@lem3585413 A B f P)). Qed.
Lemma lem3585416 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term27 A B f P) = (term136 A B f P).
Proof. exact (TRANS (@lem3585315 A B f P) (@lem3585415 A B f P)). Qed.
Lemma lem3585417 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term27 A B f P) : term136 A B f P.
Proof. exact (EQ_MP (@lem3585416 A B f P) (@lem3585225 A B f P h1)). Qed.
Lemma lem3585418 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (h1 : term134 A B x f P) : term134 A B x f P.
Proof. exact (h1). Qed.
Lemma lem3585419 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term131 A B x f P y) : term131 A B x f P y.
Proof. exact (h1). Qed.
Lemma lem3585420 {A B : Type'} (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term49 A B f x'.
Proof. exact (h1). Qed.
Lemma lem3585423 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3585430 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term59 A B P f x) = (term59 A B P f x).
Proof. exact (eq_refl (term59 A B P f x)). Qed.
Lemma lem3585431 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term61 A B P f) = (term61 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3585430 A B P f x)). Qed.
Lemma lem3585432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3585433 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term62 A B P f) = (term62 A B P f).
Proof. exact (MK_COMB (@lem3585432 A) (@lem3585431 A B P f)). Qed.
Lemma lem3585434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585435 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term71 A B P f) = (term71 A B P f).
Proof. exact (MK_COMB (@lem3585434) (@lem3585433 A B P f)). Qed.
Lemma lem3585436 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term125 A B f P y) = (term125 A B f P y).
Proof. exact (MK_COMB (@lem3585435 A B P f) (@lem3585423 B P y)). Qed.
Lemma lem3585441 {B : Type'} (P : B -> Prop) (y : B) : (term67 B P y) = (term67 B P y).
Proof. exact (eq_refl (term67 B P y)). Qed.
Lemma lem3585442 {B : Type'} (P : B -> Prop) : (term69 B P) = (term69 B P).
Proof. exact (fun_ext (fun y : B => @lem3585441 B P y)). Qed.
Lemma lem3585443 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585444 {B : Type'} (P : B -> Prop) : (term54 B P) = (term54 B P).
Proof. exact (MK_COMB (@lem3585443 B) (@lem3585442 B P)). Qed.
Lemma lem3585451 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term91 A B P f x) = (term91 A B P f x).
Proof. exact (eq_refl (term91 A B P f x)). Qed.
Lemma lem3585452 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term93 A B f x P) = (term93 A B f x P).
Proof. exact (MK_COMB (@lem3585451 A B P f x) (@lem3585444 B P)). Qed.
Lemma lem3585453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3585454 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term113 A B f x P) = (term113 A B f x P).
Proof. exact (MK_COMB (@lem3585453) (@lem3585452 A B f x P)). Qed.
Lemma lem3585455 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (y : B) : (term131 A B x f P y) = (term131 A B x f P y).
Proof. exact (MK_COMB (@lem3585454 A B f x P) (@lem3585436 A B f P y)). Qed.
Lemma lem3585456 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term131 A B x f P y) : term131 A B x f P y.
Proof. exact (EQ_MP (@lem3585455 A B x f P y) (@lem3585419 A B x f P y h1)). Qed.
Lemma lem3585465 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : ((term45 A B f x' y) = y) = ((term45 A B f x' y) = y).
Proof. exact (eq_refl ((term45 A B f x' y) = y)). Qed.
Lemma lem3585466 {A B : Type'} (f : A -> B) (x' : B -> A) : (term47 A B f x') = (term47 A B f x').
Proof. exact (fun_ext (fun y : B => @lem3585465 A B f x' y)). Qed.
Lemma lem3585467 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585468 {A B : Type'} (f : A -> B) (x' : B -> A) : (term49 A B f x') = (term49 A B f x').
Proof. exact (MK_COMB (@lem3585467 B) (@lem3585466 A B f x')). Qed.
Lemma lem3585469 {A B : Type'} (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term49 A B f x'.
Proof. exact (EQ_MP (@lem3585468 A B f x') (@lem3585420 A B f x' h1)). Qed.
Lemma lem3585470 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term93 A B f x P.
Proof. exact (h1). Qed.
Lemma lem3585471 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term125 A B f P y.
Proof. exact (h1). Qed.
Lemma lem3585472 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term54 B P.
Proof. exact (proj2 (@lem3585470 A B f x P h1)). Qed.
Lemma lem3585475 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term62 A B P f.
Proof. exact (proj1 (@lem3585471 A B f P y h1)). Qed.
Lemma lem3585488 {B : Type'} (P : B -> Prop) (y : B) : (term67 B P y) = (term67 B P y).
Proof. exact (eq_refl (term67 B P y)). Qed.
Lemma lem3585489 {B : Type'} (P : B -> Prop) : (term69 B P) = (term69 B P).
Proof. exact (fun_ext (fun y : B => @lem3585488 B P y)). Qed.
Lemma lem3585490 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585492 {B : Type'} (P : B -> Prop) : (term54 B P) = (term54 B P).
Proof. exact (MK_COMB (@lem3585490 B) (@lem3585489 B P)). Qed.
Lemma lem3585493 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term54 B P.
Proof. exact (EQ_MP (@lem3585492 B P) (@lem3585472 A B f x P h1)). Qed.
Lemma lem3585495 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : ((term45 A B f x' y) = y) = ((term45 A B f x' y) = y).
Proof. exact (eq_refl ((term45 A B f x' y) = y)). Qed.
Lemma lem3585496 {A B : Type'} (f : A -> B) (x' : B -> A) : (term47 A B f x') = (term47 A B f x').
Proof. exact (fun_ext (fun y : B => @lem3585495 A B f x' y)). Qed.
Lemma lem3585497 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3585499 {A B : Type'} (f : A -> B) (x' : B -> A) : (term49 A B f x') = (term49 A B f x').
Proof. exact (MK_COMB (@lem3585497 B) (@lem3585496 A B f x')). Qed.
Lemma lem3585500 {A B : Type'} (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term49 A B f x'.
Proof. exact (EQ_MP (@lem3585499 A B f x') (@lem3585469 A B f x' h1)). Qed.
Lemma lem3585502 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term59 A B P f x) = (term59 A B P f x).
Proof. exact (eq_refl (term59 A B P f x)). Qed.
Lemma lem3585503 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term61 A B P f) = (term61 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3585502 A B P f x)). Qed.
Lemma lem3585504 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3585506 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term62 A B P f) = (term62 A B P f).
Proof. exact (MK_COMB (@lem3585504 A) (@lem3585503 A B P f)). Qed.
Lemma lem3585507 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term62 A B P f.
Proof. exact (EQ_MP (@lem3585506 A B P f) (@lem3585475 A B f P y h1)). Qed.
Lemma lem3585515 {A B : Type'} (_38719 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term137 B P _38719.
Proof. exact (@lem3585493 A B f x P h1 _38719). Qed.
Lemma lem3585516 {B : Type'} (P : B -> Prop) (_38719 : B) : (term137 B P _38719) = (term67 B P _38719).
Proof. exact (eq_refl (term137 B P _38719)). Qed.
Lemma lem3585518 {A B : Type'} (_38720 : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term138 A B f x' _38720.
Proof. exact (@lem3585500 A B f x' h1 _38720). Qed.
Lemma lem3585519 {A B : Type'} (f : A -> B) (x' : B -> A) (_38720 : B) : (term138 A B f x' _38720) = ((term45 A B f x' _38720) = _38720).
Proof. exact (eq_refl (term138 A B f x' _38720)). Qed.
Lemma lem3585521 {A B : Type'} (_38721 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term139 A B P f _38721.
Proof. exact (@lem3585507 A B f P y h1 _38721). Qed.
Lemma lem3585522 {A B : Type'} (P : B -> Prop) (f : A -> B) (_38721 : A) : (term139 A B P f _38721) = (term59 A B P f _38721).
Proof. exact (eq_refl (term139 A B P f _38721)). Qed.
Lemma lem3585529 {A B : Type'} (_38719 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term67 B P _38719.
Proof. exact (EQ_MP (@lem3585516 B P _38719) (@lem3585515 A B _38719 f x P h1)). Qed.
Lemma lem3585533 {A B : Type'} (_38721 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term59 A B P f _38721.
Proof. exact (EQ_MP (@lem3585522 A B P f _38721) (@lem3585521 A B _38721 f P y h1)). Qed.
Lemma lem3585569 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term15 A B P f x.
Proof. exact (proj1 (@lem3585470 A B f x P h1)). Qed.
Lemma lem3585570 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term140 A B P f x.
Proof. exact (fun h0 : term59 A B P f x => @lem3585569 A B f x P h1). Qed.
Lemma lem3585572 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585573 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term140 A B P f x) = (term15 A B P f x).
Proof. exact (@lem3585572 (term15 A B P f x)). Qed.
Lemma lem3585574 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term15 A B P f x.
Proof. exact (EQ_MP (@lem3585573 A B P f x) (@lem3585570 A B f x P h1)). Qed.
Lemma lem3585577 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3585579 {B : Type'} (P : B -> Prop) (_38719 : B) : (term67 B P _38719) = (term142 B P _38719).
Proof. exact (@lem3585577 (P _38719)). Qed.
Lemma lem3585582 {A B : Type'} (_38719 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term142 B P _38719.
Proof. exact (EQ_MP (@lem3585579 B P _38719) (@lem3585529 A B _38719 f x P h1)). Qed.
Lemma lem3585583 {A B : Type'} (_38719 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term142 B P _38719.
Proof. exact (@lem3585582 A B _38719 f x P h1). Qed.
Lemma lem3585584 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term143 A B P f x.
Proof. exact (@lem3585583 A B (f x) f x P h1). Qed.
Lemma lem3585587 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : False.
Proof. exact (@lem3585584 A B f x P h1 (@lem3585574 A B f x P h1)). Qed.
Lemma lem3585588 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : term144.
Proof. exact (fun h0 : ~ False => @lem3585587 A B f x P h1). Qed.
Lemma lem3585590 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585591 : term144 = False.
Proof. exact (@lem3585590 False). Qed.
Lemma lem3585592 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term93 A B f x P) : False.
Proof. exact (EQ_MP (@lem3585591) (@lem3585588 A B f x P h1)). Qed.
Lemma lem3585593 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3585594 {B : Type'} (_38728 : B) (_38729 : B) (h1 : _38728 = _38729) : _38728 = _38729.
Proof. exact (h1). Qed.
Lemma lem3585595 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) (h1 : _38728 = _38729) : (P _38728) = (P _38729).
Proof. exact (MK_COMB (@lem3585593 B P) (@lem3585594 B _38728 _38729 h1)). Qed.
Lemma lem3585597 (b : Prop) (a : Prop) : term145 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3585598 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : term146 B _38729 P _38728.
Proof. exact (@lem3585597 (P _38729) (P _38728)). Qed.
Lemma lem3585599 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) (h1 : _38728 = _38729) : term147 B _38729 P _38728.
Proof. exact (@lem3585598 B _38729 P _38728 (@lem3585595 B P _38728 _38729 h1)). Qed.
Lemma lem3585600 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : term148 B _38729 P _38728.
Proof. exact (fun h0 : _38728 = _38729 => @lem3585599 B P _38728 _38729 h0). Qed.
Lemma lem3585602 (a : Prop) (b : Prop) : (a -> b) = (term149 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3585603 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term148 B _38729 P _38728) = (term150 B _38729 P _38728).
Proof. exact (@lem3585602 (_38728 = _38729) (term147 B _38729 P _38728)). Qed.
Lemma lem3585604 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : term150 B _38729 P _38728.
Proof. exact (EQ_MP (@lem3585603 B _38729 P _38728) (@lem3585600 B _38729 P _38728)). Qed.
Lemma lem3585622 {B : Type'} (x : B) (y : B) (z : B) : term151 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3585626 {A B : Type'} (_38720 : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' _38720) = _38720.
Proof. exact (EQ_MP (@lem3585519 A B f x' _38720) (@lem3585518 A B _38720 f x' h1)). Qed.
Lemma lem3585627 {A B : Type'} (_38720 : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' _38720) = _38720.
Proof. exact (@lem3585626 A B _38720 f x' h1). Qed.
Lemma lem3585628 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' y) = y.
Proof. exact (@lem3585627 A B y f x' h1). Qed.
Lemma lem3585629 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term152 A B f x' y.
Proof. exact (fun h0 : term153 A B f x' y => @lem3585628 A B y f x' h1). Qed.
Lemma lem3585631 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585632 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term152 A B f x' y) = ((term45 A B f x' y) = y).
Proof. exact (@lem3585631 ((term45 A B f x' y) = y)). Qed.
Lemma lem3585633 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' y) = y.
Proof. exact (EQ_MP (@lem3585632 A B f x' y) (@lem3585629 A B y f x' h1)). Qed.
Lemma lem3585635 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3585636 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3585635 B x). Qed.
Lemma lem3585637 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term45 A B f x' y) = (term45 A B f x' y).
Proof. exact (@lem3585636 B (term45 A B f x' y)). Qed.
Lemma lem3585638 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : term154 A B f x' y.
Proof. exact (fun h0 : term155 A B f x' y => @lem3585637 A B f x' y). Qed.
Lemma lem3585640 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585641 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term154 A B f x' y) = ((term45 A B f x' y) = (term45 A B f x' y)).
Proof. exact (@lem3585640 ((term45 A B f x' y) = (term45 A B f x' y))). Qed.
Lemma lem3585642 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term45 A B f x' y) = (term45 A B f x' y).
Proof. exact (EQ_MP (@lem3585641 A B f x' y) (@lem3585638 A B f x' y)). Qed.
Lemma lem3585660 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3585661 {B : Type'} (y : B) (x : B) (z : B) : (term156 B x y z) = (term157 B y x z).
Proof. exact (@lem3585660 (y = z) (term158 B x z)). Qed.
Lemma lem3585671 {B : Type'} (x : B) (y : B) : (term159 B x y) = (term159 B x y).
Proof. exact (eq_refl (term159 B x y)). Qed.
Lemma lem3585672 {B : Type'} (y : B) (x : B) (z : B) : (term151 B x y z) = (term160 B y x z).
Proof. exact (MK_COMB (@lem3585671 B x y) (@lem3585661 B y x z)). Qed.
Lemma lem3585676 (q : Prop) (p : Prop) (r : Prop) : (term161 p q r) = (term161 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3585677 {B : Type'} (y : B) (x : B) (z : B) : (term160 B y x z) = (term162 B y x z).
Proof. exact (@lem3585676 (y = z) (term158 B x y) (term158 B x z)). Qed.
Lemma lem3585699 {B : Type'} (y : B) (x : B) (z : B) : (term151 B x y z) = (term162 B y x z).
Proof. exact (TRANS (@lem3585672 B y x z) (@lem3585677 B y x z)). Qed.
Lemma lem3585700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585701 {B : Type'} (y : B) (x : B) (z : B) : (term163 B x y z) = (term164 B y x z).
Proof. exact (MK_COMB (@lem3585700) (@lem3585699 B y x z)). Qed.
Lemma lem3585723 {B : Type'} (y : B) (x : B) (z : B) : (term162 B y x z) = (term162 B y x z).
Proof. exact (eq_refl (term162 B y x z)). Qed.
Lemma lem3585724 {B : Type'} (y : B) (x : B) (z : B) : ((term151 B x y z) = (term162 B y x z)) = ((term162 B y x z) = (term162 B y x z)).
Proof. exact (MK_COMB (@lem3585701 B y x z) (@lem3585723 B y x z)). Qed.
Lemma lem3585726 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3585727 (x : Prop) : (x = x) = True.
Proof. exact (@lem3585726 Prop x). Qed.
Lemma lem3585728 {B : Type'} (y : B) (x : B) (z : B) : ((term162 B y x z) = (term162 B y x z)) = True.
Proof. exact (@lem3585727 (term162 B y x z)). Qed.
Lemma lem3585729 {B : Type'} (y : B) (x : B) (z : B) : ((term151 B x y z) = (term162 B y x z)) = True.
Proof. exact (TRANS (@lem3585724 B y x z) (@lem3585728 B y x z)). Qed.
Lemma lem3585730 {B : Type'} (y : B) (x : B) (z : B) : True = ((term151 B x y z) = (term162 B y x z)).
Proof. exact (SYM (@lem3585729 B y x z)). Qed.
Lemma lem3585731 {B : Type'} (y : B) (x : B) (z : B) : (term151 B x y z) = (term162 B y x z).
Proof. exact (EQ_MP (@lem3585730 B y x z) (@lem0)). Qed.
Lemma lem3585732 {B : Type'} (y : B) (x : B) (z : B) : term162 B y x z.
Proof. exact (EQ_MP (@lem3585731 B y x z) (@lem3585622 B x y z)). Qed.
Lemma lem3585734 (b : Prop) (a : Prop) : (a \/ b) = (term165 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3585735 {B : Type'} (x : B) (y : B) (z : B) : (term162 B y x z) = (term166 B x y z).
Proof. exact (@lem3585734 (term167 B y x z) (y = z)). Qed.
Lemma lem3585737 (a : Prop) (b : Prop) : (term168 a b) = (term169 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3585738 {B : Type'} (y : B) (x : B) (z : B) : (term170 B y x z) = (term171 B y x z).
Proof. exact (@lem3585737 (term158 B x y) (term158 B x z)). Qed.
Lemma lem3585740 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3585741 {B : Type'} (x : B) (y : B) : (term172 B x y) = (x = y).
Proof. exact (@lem3585740 (x = y)). Qed.
Lemma lem3585742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585743 {B : Type'} (x : B) (y : B) : (term173 B x y) = (term174 B x y).
Proof. exact (MK_COMB (@lem3585742) (@lem3585741 B x y)). Qed.
Lemma lem3585745 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3585746 {B : Type'} (x : B) (z : B) : (term172 B x z) = (x = z).
Proof. exact (@lem3585745 (x = z)). Qed.
Lemma lem3585747 {B : Type'} (y : B) (x : B) (z : B) : (term171 B y x z) = (term175 B y x z).
Proof. exact (MK_COMB (@lem3585743 B x y) (@lem3585746 B x z)). Qed.
Lemma lem3585748 {B : Type'} (y : B) (x : B) (z : B) : (term170 B y x z) = (term175 B y x z).
Proof. exact (TRANS (@lem3585738 B y x z) (@lem3585747 B y x z)). Qed.
Lemma lem3585749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3585750 {B : Type'} (y : B) (x : B) (z : B) : (term176 B y x z) = (term177 B y x z).
Proof. exact (MK_COMB (@lem3585749) (@lem3585748 B y x z)). Qed.
Lemma lem3585751 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3585752 {B : Type'} (x : B) (y : B) (z : B) : (term166 B x y z) = (term178 B x y z).
Proof. exact (MK_COMB (@lem3585750 B y x z) (@lem3585751 B y z)). Qed.
Lemma lem3585753 {B : Type'} (x : B) (y : B) (z : B) : (term162 B y x z) = (term178 B x y z).
Proof. exact (TRANS (@lem3585735 B x y z) (@lem3585752 B x y z)). Qed.
Lemma lem3585755 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term179 A B f x' y.
Proof. exact (conj (@lem3585633 A B y f x' h1) (@lem3585642 A B f x' y)). Qed.
Lemma lem3585757 {B : Type'} (x : B) (y : B) (z : B) : term178 B x y z.
Proof. exact (EQ_MP (@lem3585753 B x y z) (@lem3585732 B y x z)). Qed.
Lemma lem3585758 {B : Type'} (x : B) (y : B) (z : B) : term178 B x y z.
Proof. exact (@lem3585757 B x y z). Qed.
Lemma lem3585759 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : term180 A B f x' y.
Proof. exact (@lem3585758 B (term45 A B f x' y) y (term45 A B f x' y)). Qed.
Lemma lem3585762 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : y = (term45 A B f x' y).
Proof. exact (@lem3585759 A B f x' y (@lem3585755 A B y f x' h1)). Qed.
Lemma lem3585763 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : y = (term45 A B f x' y).
Proof. exact (@lem3585762 A B y f x' h1). Qed.
Lemma lem3585764 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term181 A B f x' y.
Proof. exact (fun h0 : term182 A B f x' y => @lem3585763 A B y f x' h1). Qed.
Lemma lem3585766 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585767 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term181 A B f x' y) = (y = (term45 A B f x' y)).
Proof. exact (@lem3585766 (y = (term45 A B f x' y))). Qed.
Lemma lem3585768 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : y = (term45 A B f x' y).
Proof. exact (EQ_MP (@lem3585767 A B f x' y) (@lem3585764 A B y f x' h1)). Qed.
Lemma lem3585770 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : P y.
Proof. exact (proj2 (@lem3585471 A B f P y h1)). Qed.
Lemma lem3585771 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term183 B P y.
Proof. exact (fun h0 : term67 B P y => @lem3585770 A B f P y h1). Qed.
Lemma lem3585773 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585774 {B : Type'} (P : B -> Prop) (y : B) : (term183 B P y) = (P y).
Proof. exact (@lem3585773 (P y)). Qed.
Lemma lem3585775 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : P y.
Proof. exact (EQ_MP (@lem3585774 B P y) (@lem3585771 A B f P y h1)). Qed.
Lemma lem3585781 (q : Prop) (p : Prop) (r : Prop) : (term161 p q r) = (term161 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3585782 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term150 B _38729 P _38728) = (term184 B _38729 P _38728).
Proof. exact (@lem3585781 (P _38729) (term158 B _38728 _38729) (term67 B P _38728)). Qed.
Lemma lem3585796 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3585797 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : (term185 B _38729 P _38728) = (term186 B P _38728 _38729).
Proof. exact (@lem3585796 (term67 B P _38728) (term158 B _38728 _38729)). Qed.
Lemma lem3585805 {B : Type'} (P : B -> Prop) (_38729 : B) : (term187 B P _38729) = (term187 B P _38729).
Proof. exact (eq_refl (term187 B P _38729)). Qed.
Lemma lem3585806 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : (term184 B _38729 P _38728) = (term188 B P _38728 _38729).
Proof. exact (MK_COMB (@lem3585805 B P _38729) (@lem3585797 B P _38728 _38729)). Qed.
Lemma lem3585817 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : (term150 B _38729 P _38728) = (term188 B P _38728 _38729).
Proof. exact (TRANS (@lem3585782 B _38729 P _38728) (@lem3585806 B P _38728 _38729)). Qed.
Lemma lem3585818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3585819 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : (term189 B _38729 P _38728) = (term190 B P _38728 _38729).
Proof. exact (MK_COMB (@lem3585818) (@lem3585817 B P _38728 _38729)). Qed.
Lemma lem3585833 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3585834 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : (term185 B _38729 P _38728) = (term186 B P _38728 _38729).
Proof. exact (@lem3585833 (term67 B P _38728) (term158 B _38728 _38729)). Qed.
Lemma lem3585842 {B : Type'} (P : B -> Prop) (_38729 : B) : (term187 B P _38729) = (term187 B P _38729).
Proof. exact (eq_refl (term187 B P _38729)). Qed.
Lemma lem3585843 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : (term184 B _38729 P _38728) = (term188 B P _38728 _38729).
Proof. exact (MK_COMB (@lem3585842 B P _38729) (@lem3585834 B P _38728 _38729)). Qed.
Lemma lem3585854 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : ((term150 B _38729 P _38728) = (term184 B _38729 P _38728)) = ((term188 B P _38728 _38729) = (term188 B P _38728 _38729)).
Proof. exact (MK_COMB (@lem3585819 B P _38728 _38729) (@lem3585843 B P _38728 _38729)). Qed.
Lemma lem3585856 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3585857 (x : Prop) : (x = x) = True.
Proof. exact (@lem3585856 Prop x). Qed.
Lemma lem3585858 {B : Type'} (P : B -> Prop) (_38728 : B) (_38729 : B) : ((term188 B P _38728 _38729) = (term188 B P _38728 _38729)) = True.
Proof. exact (@lem3585857 (term188 B P _38728 _38729)). Qed.
Lemma lem3585859 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : ((term150 B _38729 P _38728) = (term184 B _38729 P _38728)) = True.
Proof. exact (TRANS (@lem3585854 B P _38728 _38729) (@lem3585858 B P _38728 _38729)). Qed.
Lemma lem3585860 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : True = ((term150 B _38729 P _38728) = (term184 B _38729 P _38728)).
Proof. exact (SYM (@lem3585859 B _38729 P _38728)). Qed.
Lemma lem3585861 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term150 B _38729 P _38728) = (term184 B _38729 P _38728).
Proof. exact (EQ_MP (@lem3585860 B _38729 P _38728) (@lem0)). Qed.
Lemma lem3585862 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : term184 B _38729 P _38728.
Proof. exact (EQ_MP (@lem3585861 B _38729 P _38728) (@lem3585604 B _38729 P _38728)). Qed.
Lemma lem3585864 (b : Prop) (a : Prop) : (a \/ b) = (term165 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3585865 {B : Type'} (_38728 : B) (P : B -> Prop) (_38729 : B) : (term184 B _38729 P _38728) = (term191 B _38728 P _38729).
Proof. exact (@lem3585864 (term185 B _38729 P _38728) (P _38729)). Qed.
Lemma lem3585867 (a : Prop) (b : Prop) : (term168 a b) = (term169 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3585868 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term192 B _38729 P _38728) = (term193 B _38729 P _38728).
Proof. exact (@lem3585867 (term158 B _38728 _38729) (term67 B P _38728)). Qed.
Lemma lem3585870 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3585871 {B : Type'} (_38728 : B) (_38729 : B) : (term172 B _38728 _38729) = (_38728 = _38729).
Proof. exact (@lem3585870 (_38728 = _38729)). Qed.
Lemma lem3585872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3585873 {B : Type'} (_38728 : B) (_38729 : B) : (term173 B _38728 _38729) = (term174 B _38728 _38729).
Proof. exact (MK_COMB (@lem3585872) (@lem3585871 B _38728 _38729)). Qed.
Lemma lem3585875 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3585876 {B : Type'} (P : B -> Prop) (_38728 : B) : (term194 B P _38728) = (P _38728).
Proof. exact (@lem3585875 (P _38728)). Qed.
Lemma lem3585877 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term193 B _38729 P _38728) = (term195 B _38729 P _38728).
Proof. exact (MK_COMB (@lem3585873 B _38728 _38729) (@lem3585876 B P _38728)). Qed.
Lemma lem3585878 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term192 B _38729 P _38728) = (term195 B _38729 P _38728).
Proof. exact (TRANS (@lem3585868 B _38729 P _38728) (@lem3585877 B _38729 P _38728)). Qed.
Lemma lem3585879 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3585880 {B : Type'} (_38729 : B) (P : B -> Prop) (_38728 : B) : (term196 B _38729 P _38728) = (term197 B _38729 P _38728).
Proof. exact (MK_COMB (@lem3585879) (@lem3585878 B _38729 P _38728)). Qed.
Lemma lem3585881 {B : Type'} (P : B -> Prop) (_38729 : B) : (P _38729) = (P _38729).
Proof. exact (eq_refl (P _38729)). Qed.
Lemma lem3585882 {B : Type'} (_38728 : B) (P : B -> Prop) (_38729 : B) : (term191 B _38728 P _38729) = (term198 B _38728 P _38729).
Proof. exact (MK_COMB (@lem3585880 B _38729 P _38728) (@lem3585881 B P _38729)). Qed.
Lemma lem3585883 {B : Type'} (_38728 : B) (P : B -> Prop) (_38729 : B) : (term184 B _38729 P _38728) = (term198 B _38728 P _38729).
Proof. exact (TRANS (@lem3585865 B _38728 P _38729) (@lem3585882 B _38728 P _38729)). Qed.
Lemma lem3585885 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : term199 A B f x' P y.
Proof. exact (conj (@lem3585768 A B y f x' h1) (@lem3585775 A B f P y h2)). Qed.
Lemma lem3585887 {B : Type'} (_38728 : B) (P : B -> Prop) (_38729 : B) : term198 B _38728 P _38729.
Proof. exact (EQ_MP (@lem3585883 B _38728 P _38729) (@lem3585862 B _38729 P _38728)). Qed.
Lemma lem3585888 {B : Type'} (_38728 : B) (P : B -> Prop) (_38729 : B) : term198 B _38728 P _38729.
Proof. exact (@lem3585887 B _38728 P _38729). Qed.
Lemma lem3585889 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : B -> A) (y : B) : term200 A B P f x' y.
Proof. exact (@lem3585888 B y P (term45 A B f x' y)). Qed.
Lemma lem3585892 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : term201 A B P f x' y.
Proof. exact (@lem3585889 A B P f x' y (@lem3585885 A B x' f P y h1 h2)). Qed.
Lemma lem3585893 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : term202 A B P f x' y.
Proof. exact (fun h0 : term203 A B P f x' y => @lem3585892 A B x' f P y h1 h2). Qed.
Lemma lem3585895 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585896 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term202 A B P f x' y) = (term201 A B P f x' y).
Proof. exact (@lem3585895 (term201 A B P f x' y)). Qed.
Lemma lem3585897 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : term201 A B P f x' y.
Proof. exact (EQ_MP (@lem3585896 A B P f x' y) (@lem3585893 A B x' f P y h1 h2)). Qed.
Lemma lem3585900 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3585902 {A B : Type'} (P : B -> Prop) (f : A -> B) (_38721 : A) : (term59 A B P f _38721) = (term143 A B P f _38721).
Proof. exact (@lem3585900 (term15 A B P f _38721)). Qed.
Lemma lem3585905 {A B : Type'} (_38721 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term143 A B P f _38721.
Proof. exact (EQ_MP (@lem3585902 A B P f _38721) (@lem3585533 A B _38721 f P y h1)). Qed.
Lemma lem3585906 {A B : Type'} (_38721 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term143 A B P f _38721.
Proof. exact (@lem3585905 A B _38721 f P y h1). Qed.
Lemma lem3585907 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term125 A B f P y) : term204 A B P f x' y.
Proof. exact (@lem3585906 A B (x' y) f P y h1). Qed.
Lemma lem3585910 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : False.
Proof. exact (@lem3585907 A B x' f P y h2 (@lem3585897 A B x' f P y h1 h2)). Qed.
Lemma lem3585911 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : term144.
Proof. exact (fun h0 : ~ False => @lem3585910 A B x' f P y h1 h2). Qed.
Lemma lem3585913 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585914 : term144 = False.
Proof. exact (@lem3585913 False). Qed.
Lemma lem3585915 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : False.
Proof. exact (EQ_MP (@lem3585914) (@lem3585911 A B x' f P y h1 h2)). Qed.
Lemma lem3585916 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : (term49 A B f x') = False.
Proof. exact (prop_ext (fun h3 : term49 A B f x' => @lem3585915 A B x' f P y h1 h2) (fun h3 : False => @lem3585500 A B f x' h1)). Qed.
Lemma lem3585917 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term125 A B f P y) : False.
Proof. exact (EQ_MP (@lem3585916 A B x' f P y h1 h2) (@lem3585500 A B f x' h1)). Qed.
Lemma lem3585918 {A B : Type'} (x' : B -> A) (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term131 A B x f P y) : False.
Proof. exact (or_elim (@lem3585456 A B x f P y h2) (fun h0 : term93 A B f x P => @lem3585592 A B f x P h0) (fun h0 : term125 A B f P y => @lem3585917 A B x' f P y h1 h0)). Qed.
Lemma lem3585919 {A B : Type'} (x' : B -> A) (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term131 A B x f P y) : (term49 A B f x') = False.
Proof. exact (prop_ext (fun h3 : term49 A B f x' => @lem3585918 A B x' x f P y h1 h2) (fun h3 : False => @lem3585469 A B f x' h1)). Qed.
Lemma lem3585920 {A B : Type'} (x' : B -> A) (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term131 A B x f P y) : False.
Proof. exact (EQ_MP (@lem3585919 A B x' x f P y h1 h2) (@lem3585469 A B f x' h1)). Qed.
Lemma lem3585921 {A B : Type'} (x' : B -> A) (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term131 A B x f P y) : (term131 A B x f P y) = False.
Proof. exact (prop_ext (fun h3 : term131 A B x f P y => @lem3585920 A B x' x f P y h1 h2) (fun h3 : False => @lem3585456 A B x f P y h2)). Qed.
Lemma lem3585922 {A B : Type'} (x' : B -> A) (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term131 A B x f P y) : False.
Proof. exact (EQ_MP (@lem3585921 A B x' x f P y h1 h2) (@lem3585456 A B x f P y h2)). Qed.
Lemma lem3585923 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term24 A B f) (h2 : term131 A B x f P y) : False.
Proof. exact (ex_elim (@lem3585274 A B f h1) (fun x' : B -> A => fun h0 : term51 A B f x' => @lem3585922 A B x' x f P y h0 h2)). Qed.
Lemma lem3585924 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term134 A B x f P) : False.
Proof. exact (ex_elim (@lem3585418 A B x f P h2) (fun y : B => fun h0 : term133 A B x f P y => @lem3585923 A B x f P y h1 h0)). Qed.
Lemma lem3585925 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term27 A B f P) : False.
Proof. exact (ex_elim (@lem3585417 A B f P h2) (fun x : A => fun h0 : term135 A B f P x => @lem3585924 A B x f P h1 h0)). Qed.
Lemma lem3585926 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term27 A B f P) : (term27 A B f P) = False.
Proof. exact (prop_ext (fun h3 : term27 A B f P => @lem3585925 A B f P h1 h2) (fun h3 : False => @lem3585225 A B f P h2)). Qed.
Lemma lem3585927 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term27 A B f P) : False.
Proof. exact (EQ_MP (@lem3585926 A B f P h1 h2) (@lem3585225 A B f P h2)). Qed.
Lemma lem3585928 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term24 A B f) : term26 A B f P.
Proof. exact (fun h0 : term27 A B f P => @lem3585927 A B f P h1 h0). Qed.
Lemma lem3585929 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term24 A B f) : (term17 A B P f) = (term14 B P).
Proof. exact (EQ_MP (@lem3585224 A B f P) (@lem3585928 A B P f h1)). Qed.
Lemma lem3585934 {A B : Type'} (f : A -> B) (h1 : term24 A B f) : term20 A B f.
Proof. exact (fun P : B -> Prop => @lem3585929 A B P f h1). Qed.
Lemma lem3585935 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (fun h0 : term24 A B f => @lem3585934 A B f h0). Qed.
Lemma lem3585940 {A B : Type'} : term12 A B.
Proof. exact (fun f : A -> B => @lem3585935 A B f). Qed.
Lemma lem3585941 {A B : Type'} : term11 A B.
Proof. exact (EQ_MP (@lem3585219 A B) (@lem3585940 A B)). Qed.
Lemma lem3585942 {A B : Type'} (f : A -> B) : term205 A B f.
Proof. exact (@lem3585941 A B f). Qed.
Lemma lem3585943 {A B : Type'} (f : A -> B) : (term205 A B f) = (term2 A B f).
Proof. exact (eq_refl (term205 A B f)). Qed.
Lemma lem3585944 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem3585943 A B f) (@lem3585942 A B f)). Qed.
Lemma lem3585946 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (@lem3585106 A B f (@lem3585944 A B f)). Qed.
Lemma lem3585947 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : False.
Proof. exact (@lem3585946 A B f (@lem3585090 A B f h1)). Qed.
Lemma lem3585948 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : (term3 A B f) = False.
Proof. exact (prop_ext (fun h2 : term3 A B f => @lem3585947 A B f h1) (fun h2 : False => @lem3585090 A B f h1)). Qed.
Lemma lem3585949 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : False.
Proof. exact (EQ_MP (@lem3585948 A B f h1) (@lem3585090 A B f h1)). Qed.
Lemma lem3585950 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (fun h0 : term3 A B f => @lem3585949 A B f h0). Qed.
Lemma lem3585951 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem3585089 A B f) (@lem3585950 A B f)). Qed.
Lemma lem3585952 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : term20 A B f.
Proof. exact (h1). Qed.
Lemma lem3585953 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : term206 A B f.
Proof. exact (@lem3585952 A B f h1 (term207 A B f)). Qed.
Lemma lem3585954 {A B : Type'} (f : A -> B) : (term206 A B f) = ((term208 A B f) = (term209 A B f)).
Proof. exact (eq_refl (term206 A B f)). Qed.
Lemma lem3585955 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : (term208 A B f) = (term209 A B f).
Proof. exact (EQ_MP (@lem3585954 A B f) (@lem3585953 A B f h1)). Qed.
Lemma lem3585957 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3585958 {A B : Type'} (f : A -> B) : (term210 A B f) = (term211 A B f).
Proof. exact (@lem3585957 (term210 A B f)). Qed.
Lemma lem3585959 {A B : Type'} (f : A -> B) : (term211 A B f) = (term210 A B f).
Proof. exact (SYM (@lem3585958 A B f)). Qed.
Lemma lem3585960 {A B : Type'} (f : A -> B) (h1 : term212 A B f) : term212 A B f.
Proof. exact (h1). Qed.
Lemma lem3585963 {A B : Type'} (f : A -> B) (h1 : term211 A B f) : term211 A B f.
Proof. exact (h1). Qed.
Lemma lem3585964 {A B : Type'} (f : A -> B) : term213 A B f.
Proof. exact (fun h0 : term211 A B f => @lem3585963 A B f h0). Qed.
Lemma lem3585965 {A B : Type'} (f : A -> B) (h1 : term213 A B f) : term213 A B f.
Proof. exact (h1). Qed.
Lemma lem3585966 {A B : Type'} (f : A -> B) (h1 : term211 A B f) : term211 A B f.
Proof. exact (h1). Qed.
Lemma lem3585967 {A B : Type'} (f : A -> B) (h1 : term211 A B f) (h2 : term213 A B f) : term211 A B f.
Proof. exact (@lem3585965 A B f h2 (@lem3585966 A B f h1)). Qed.
Lemma lem3585968 {A B : Type'} (f : A -> B) (h1 : term211 A B f) : term214 A B f.
Proof. exact (fun h0 : term213 A B f => @lem3585967 A B f h1 h0). Qed.
Lemma lem3585969 {A B : Type'} (f : A -> B) (h1 : term213 A B f) : term213 A B f.
Proof. exact (h1). Qed.
Lemma lem3585970 {A B : Type'} (f : A -> B) (h1 : term211 A B f) (h2 : term213 A B f) : term211 A B f.
Proof. exact (@lem3585968 A B f h1 (@lem3585969 A B f h2)). Qed.
Lemma lem3585971 {A B : Type'} (f : A -> B) (h1 : term213 A B f) : term213 A B f.
Proof. exact (fun h0 : term211 A B f => @lem3585970 A B f h0 h1). Qed.
Lemma lem3585972 {A B : Type'} (f : A -> B) : term215 A B f.
Proof. exact (fun h0 : term213 A B f => @lem3585971 A B f h0). Qed.
Lemma lem3585975 {A B : Type'} (f : A -> B) : term213 A B f.
Proof. exact (@lem3585972 A B f (@lem3585964 A B f)). Qed.
Lemma lem3585976 {A B : Type'} (f : A -> B) : term213 A B f.
Proof. exact (@lem3585975 A B f). Qed.
Lemma lem3585982 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3585983 {A B : Type'} (f : A -> B) : (term211 A B f) = (term216 A B f).
Proof. exact (@lem3585982 (term212 A B f)). Qed.
Lemma lem3585985 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3585986 {A B : Type'} (f : A -> B) : (term216 A B f) = (term210 A B f).
Proof. exact (@lem3585985 (term210 A B f)). Qed.
Lemma lem3585989 {A B : Type'} (f : A -> B) : (term211 A B f) = (term210 A B f).
Proof. exact (TRANS (@lem3585983 A B f) (@lem3585986 A B f)). Qed.
Lemma lem3586014 {A B : Type'} : (term217 A B) = (term218 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3585989 A B f)). Qed.
Lemma lem3586015 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3586016 {A B : Type'} : (term219 A B) = (term220 A B).
Proof. exact (MK_COMB (@lem3586015 A B) (@lem3586014 A B)). Qed.
Lemma lem3586021 {A B : Type'} (f : A -> B) (x : A) : (term221 A B f x) = (term222 A B f x).
Proof. exact (eq_refl (term221 A B f x)). Qed.
Lemma lem3586022 {A B : Type'} (f : A -> B) : (term223 A B f) = (term224 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586021 A B f x)). Qed.
Lemma lem3586023 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586024 {A B : Type'} (f : A -> B) : (term208 A B f) = (term225 A B f).
Proof. exact (MK_COMB (@lem3586023 A) (@lem3586022 A B f)). Qed.
Lemma lem3586025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586026 {A B : Type'} (f : A -> B) : (term226 A B f) = (term227 A B f).
Proof. exact (MK_COMB (@lem3586025) (@lem3586024 A B f)). Qed.
Lemma lem3586027 {A B : Type'} (f : A -> B) (y : B) : (term228 A B f y) = (term229 A B f y).
Proof. exact (eq_refl (term228 A B f y)). Qed.
Lemma lem3586028 {A B : Type'} (f : A -> B) : (term230 A B f) = (term207 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586027 A B f y)). Qed.
Lemma lem3586029 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586030 {A B : Type'} (f : A -> B) : (term209 A B f) = (term231 A B f).
Proof. exact (MK_COMB (@lem3586029 B) (@lem3586028 A B f)). Qed.
Lemma lem3586031 {A B : Type'} (f : A -> B) : ((term208 A B f) = (term209 A B f)) = ((term225 A B f) = (term231 A B f)).
Proof. exact (MK_COMB (@lem3586026 A B f) (@lem3586030 A B f)). Qed.
Lemma lem3586032 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3586033 {A B : Type'} (f : A -> B) : (term232 A B f) = (term233 A B f).
Proof. exact (MK_COMB (@lem3586032) (@lem3586031 A B f)). Qed.
Lemma lem3586034 {A B : Type'} (f : A -> B) : (term24 A B f) = (term24 A B f).
Proof. exact (eq_refl (term24 A B f)). Qed.
Lemma lem3586035 {A B : Type'} (f : A -> B) : (term210 A B f) = (term234 A B f).
Proof. exact (MK_COMB (@lem3586033 A B f) (@lem3586034 A B f)). Qed.
Lemma lem3586036 {A B : Type'} : (term218 A B) = (term235 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3586035 A B f)). Qed.
Lemma lem3586037 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3586038 {A B : Type'} : (term220 A B) = (term236 A B).
Proof. exact (MK_COMB (@lem3586037 A B) (@lem3586036 A B)). Qed.
Lemma lem3586041 {A B : Type'} : (term219 A B) = (term236 A B).
Proof. exact (TRANS (@lem3586016 A B) (@lem3586038 A B)). Qed.
Lemma lem3586042 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3586043 {A B : Type'} (f : A -> B) (y : B) : (term21 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586042 A B f x y)). Qed.
Lemma lem3586044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586045 {A B : Type'} (f : A -> B) (y : B) : (term22 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3586044 A) (@lem3586043 A B f y)). Qed.
Lemma lem3586046 {A B : Type'} (f : A -> B) : (term23 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586045 A B f y)). Qed.
Lemma lem3586047 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586048 {A B : Type'} (f : A -> B) : (term24 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3586047 B) (@lem3586046 A B f)). Qed.
Lemma lem3586051 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term237 A B f x y) = (term237 A B f x y).
Proof. exact (eq_refl (term237 A B f x y)). Qed.
Lemma lem3586052 {A B : Type'} (f : A -> B) (y : B) : (term238 A B f y) = (term238 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586051 A B f x y)). Qed.
Lemma lem3586053 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586054 {A B : Type'} (f : A -> B) (y : B) : (term229 A B f y) = (term229 A B f y).
Proof. exact (MK_COMB (@lem3586053 A) (@lem3586052 A B f y)). Qed.
Lemma lem3586055 {A B : Type'} (f : A -> B) : (term207 A B f) = (term207 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586054 A B f y)). Qed.
Lemma lem3586056 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586057 {A B : Type'} (f : A -> B) : (term231 A B f) = (term231 A B f).
Proof. exact (MK_COMB (@lem3586056 B) (@lem3586055 A B f)). Qed.
Lemma lem3586060 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term239 A B x' f x) = (term239 A B x' f x).
Proof. exact (eq_refl (term239 A B x' f x)). Qed.
Lemma lem3586061 {A B : Type'} (f : A -> B) (x : A) : (term240 A B f x) = (term240 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3586060 A B x' f x)). Qed.
Lemma lem3586062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586063 {A B : Type'} (f : A -> B) (x : A) : (term222 A B f x) = (term222 A B f x).
Proof. exact (MK_COMB (@lem3586062 A) (@lem3586061 A B f x)). Qed.
Lemma lem3586064 {A B : Type'} (f : A -> B) : (term224 A B f) = (term224 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586063 A B f x)). Qed.
Lemma lem3586065 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586066 {A B : Type'} (f : A -> B) : (term225 A B f) = (term225 A B f).
Proof. exact (MK_COMB (@lem3586065 A) (@lem3586064 A B f)). Qed.
Lemma lem3586067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586068 {A B : Type'} (f : A -> B) : (term227 A B f) = (term227 A B f).
Proof. exact (MK_COMB (@lem3586067) (@lem3586066 A B f)). Qed.
Lemma lem3586069 {A B : Type'} (f : A -> B) : ((term225 A B f) = (term231 A B f)) = ((term225 A B f) = (term231 A B f)).
Proof. exact (MK_COMB (@lem3586068 A B f) (@lem3586057 A B f)). Qed.
Lemma lem3586070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3586071 {A B : Type'} (f : A -> B) : (term233 A B f) = (term233 A B f).
Proof. exact (MK_COMB (@lem3586070) (@lem3586069 A B f)). Qed.
Lemma lem3586072 {A B : Type'} (f : A -> B) : (term234 A B f) = (term234 A B f).
Proof. exact (MK_COMB (@lem3586071 A B f) (@lem3586048 A B f)). Qed.
Lemma lem3586073 {A B : Type'} : (term235 A B) = (term235 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3586072 A B f)). Qed.
Lemma lem3586074 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3586075 {A B : Type'} : (term236 A B) = (term236 A B).
Proof. exact (MK_COMB (@lem3586074 A B) (@lem3586073 A B)). Qed.
Lemma lem3586122 {A B : Type'} : (term219 A B) = (term236 A B).
Proof. exact (TRANS (@lem3586041 A B) (@lem3586075 A B)). Qed.
Lemma lem3586123 {A B : Type'} : (term236 A B) = (term219 A B).
Proof. exact (SYM (@lem3586122 A B)). Qed.
Lemma lem3586124 {A B : Type'} (f : A -> B) (h1 : (term225 A B f) = (term231 A B f)) : (term225 A B f) = (term231 A B f).
Proof. exact (h1). Qed.
Lemma lem3586126 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3586127 {A B : Type'} (f : A -> B) (y : B) : (term22 A B f y) = (term241 A B f y).
Proof. exact (@lem3586126 (term22 A B f y)). Qed.
Lemma lem3586128 {A B : Type'} (f : A -> B) (y : B) : (term241 A B f y) = (term22 A B f y).
Proof. exact (SYM (@lem3586127 A B f y)). Qed.
Lemma lem3586129 {A B : Type'} (f : A -> B) (y : B) (h1 : term242 A B f y) : term242 A B f y.
Proof. exact (h1). Qed.
Lemma lem3586130 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term239 A B x' f x) = (term239 A B x' f x).
Proof. exact (eq_refl (term239 A B x' f x)). Qed.
Lemma lem3586133 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term243 A B x' f x) = ((f x') = (f x)).
Proof. exact (@lem16933 ((f x') = (f x))). Qed.
Lemma lem3586134 {A : Type'} (P : A -> Prop) : (term244 A P) = (term245 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3586135 {A B : Type'} (f : A -> B) (x : A) : (term246 A B f x) = (term247 A B f x).
Proof. exact (@lem3586134 A (term240 A B f x)). Qed.
Lemma lem3586136 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term248 A B f x x') = (term239 A B x' f x).
Proof. exact (eq_refl (term248 A B f x x')). Qed.
Lemma lem3586137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3586138 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term249 A B f x x') = (term243 A B x' f x).
Proof. exact (MK_COMB (@lem3586137) (@lem3586136 A B x' f x)). Qed.
Lemma lem3586139 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term249 A B f x x') = ((f x') = (f x)).
Proof. exact (TRANS (@lem3586138 A B x' f x) (@lem3586133 A B x' f x)). Qed.
Lemma lem3586140 {A B : Type'} (f : A -> B) (x : A) : (term250 A B f x) = (term251 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3586139 A B x' f x)). Qed.
Lemma lem3586141 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586142 {A B : Type'} (f : A -> B) (x : A) : (term247 A B f x) = (term252 A B f x).
Proof. exact (MK_COMB (@lem3586141 A) (@lem3586140 A B f x)). Qed.
Lemma lem3586143 {A B : Type'} (f : A -> B) (x : A) : (term246 A B f x) = (term252 A B f x).
Proof. exact (TRANS (@lem3586135 A B f x) (@lem3586142 A B f x)). Qed.
Lemma lem3586144 {A B : Type'} (f : A -> B) (x : A) : (term240 A B f x) = (term240 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3586130 A B x' f x)). Qed.
Lemma lem3586145 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586146 {A B : Type'} (f : A -> B) (x : A) : (term222 A B f x) = (term222 A B f x).
Proof. exact (MK_COMB (@lem3586145 A) (@lem3586144 A B f x)). Qed.
Lemma lem3586147 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3586148 {A B : Type'} (f : A -> B) : (term253 A B f) = (term254 A B f).
Proof. exact (@lem3586147 A (term224 A B f)). Qed.
Lemma lem3586149 {A B : Type'} (f : A -> B) (x : A) : (term255 A B f x) = (term222 A B f x).
Proof. exact (eq_refl (term255 A B f x)). Qed.
Lemma lem3586150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3586151 {A B : Type'} (f : A -> B) (x : A) : (term256 A B f x) = (term246 A B f x).
Proof. exact (MK_COMB (@lem3586150) (@lem3586149 A B f x)). Qed.
Lemma lem3586152 {A B : Type'} (f : A -> B) (x : A) : (term256 A B f x) = (term252 A B f x).
Proof. exact (TRANS (@lem3586151 A B f x) (@lem3586143 A B f x)). Qed.
Lemma lem3586153 {A B : Type'} (f : A -> B) : (term257 A B f) = (term258 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586152 A B f x)). Qed.
Lemma lem3586154 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586155 {A B : Type'} (f : A -> B) : (term254 A B f) = (term259 A B f).
Proof. exact (MK_COMB (@lem3586154 A) (@lem3586153 A B f)). Qed.
Lemma lem3586156 {A B : Type'} (f : A -> B) : (term253 A B f) = (term259 A B f).
Proof. exact (TRANS (@lem3586148 A B f) (@lem3586155 A B f)). Qed.
Lemma lem3586157 {A B : Type'} (f : A -> B) : (term224 A B f) = (term224 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586146 A B f x)). Qed.
Lemma lem3586158 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586159 {A B : Type'} (f : A -> B) : (term225 A B f) = (term225 A B f).
Proof. exact (MK_COMB (@lem3586158 A) (@lem3586157 A B f)). Qed.
Lemma lem3586160 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term237 A B f x y) = (term237 A B f x y).
Proof. exact (eq_refl (term237 A B f x y)). Qed.
Lemma lem3586163 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term260 A B f x y) = ((f x) = y).
Proof. exact (@lem16933 ((f x) = y)). Qed.
Lemma lem3586164 {A : Type'} (P : A -> Prop) : (term244 A P) = (term245 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3586165 {A B : Type'} (f : A -> B) (y : B) : (term261 A B f y) = (term262 A B f y).
Proof. exact (@lem3586164 A (term238 A B f y)). Qed.
Lemma lem3586166 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term263 A B f y x) = (term237 A B f x y).
Proof. exact (eq_refl (term263 A B f y x)). Qed.
Lemma lem3586167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3586168 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term264 A B f y x) = (term260 A B f x y).
Proof. exact (MK_COMB (@lem3586167) (@lem3586166 A B f x y)). Qed.
Lemma lem3586169 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term264 A B f y x) = ((f x) = y).
Proof. exact (TRANS (@lem3586168 A B f x y) (@lem3586163 A B f x y)). Qed.
Lemma lem3586170 {A B : Type'} (f : A -> B) (y : B) : (term265 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586169 A B f x y)). Qed.
Lemma lem3586171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586172 {A B : Type'} (f : A -> B) (y : B) : (term262 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3586171 A) (@lem3586170 A B f y)). Qed.
Lemma lem3586173 {A B : Type'} (f : A -> B) (y : B) : (term261 A B f y) = (term22 A B f y).
Proof. exact (TRANS (@lem3586165 A B f y) (@lem3586172 A B f y)). Qed.
Lemma lem3586174 {A B : Type'} (f : A -> B) (y : B) : (term238 A B f y) = (term238 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586160 A B f x y)). Qed.
Lemma lem3586175 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586176 {A B : Type'} (f : A -> B) (y : B) : (term229 A B f y) = (term229 A B f y).
Proof. exact (MK_COMB (@lem3586175 A) (@lem3586174 A B f y)). Qed.
Lemma lem3586177 {B : Type'} (P : B -> Prop) : (term53 B P) = (term54 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3586178 {A B : Type'} (f : A -> B) : (term266 A B f) = (term267 A B f).
Proof. exact (@lem3586177 B (term207 A B f)). Qed.
Lemma lem3586179 {A B : Type'} (f : A -> B) (y : B) : (term228 A B f y) = (term229 A B f y).
Proof. exact (eq_refl (term228 A B f y)). Qed.
Lemma lem3586180 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3586181 {A B : Type'} (f : A -> B) (y : B) : (term268 A B f y) = (term261 A B f y).
Proof. exact (MK_COMB (@lem3586180) (@lem3586179 A B f y)). Qed.
Lemma lem3586182 {A B : Type'} (f : A -> B) (y : B) : (term268 A B f y) = (term22 A B f y).
Proof. exact (TRANS (@lem3586181 A B f y) (@lem3586173 A B f y)). Qed.
Lemma lem3586183 {A B : Type'} (f : A -> B) : (term269 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586182 A B f y)). Qed.
Lemma lem3586184 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586185 {A B : Type'} (f : A -> B) : (term267 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3586184 B) (@lem3586183 A B f)). Qed.
Lemma lem3586186 {A B : Type'} (f : A -> B) : (term266 A B f) = (term24 A B f).
Proof. exact (TRANS (@lem3586178 A B f) (@lem3586185 A B f)). Qed.
Lemma lem3586187 {A B : Type'} (f : A -> B) : (term207 A B f) = (term207 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586176 A B f y)). Qed.
Lemma lem3586188 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586189 {A B : Type'} (f : A -> B) : (term231 A B f) = (term231 A B f).
Proof. exact (MK_COMB (@lem3586188 B) (@lem3586187 A B f)). Qed.
Lemma lem3586190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586191 {A B : Type'} (f : A -> B) : (term270 A B f) = (term271 A B f).
Proof. exact (MK_COMB (@lem3586190) (@lem3586156 A B f)). Qed.
Lemma lem3586192 {A B : Type'} (f : A -> B) : (term272 A B f) = (term273 A B f).
Proof. exact (MK_COMB (@lem3586191 A B f) (@lem3586186 A B f)). Qed.
Lemma lem3586193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586194 {A B : Type'} (f : A -> B) : (term274 A B f) = (term274 A B f).
Proof. exact (MK_COMB (@lem3586193) (@lem3586159 A B f)). Qed.
Lemma lem3586195 {A B : Type'} (f : A -> B) : (term275 A B f) = (term275 A B f).
Proof. exact (MK_COMB (@lem3586194 A B f) (@lem3586189 A B f)). Qed.
Lemma lem3586196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586197 {A B : Type'} (f : A -> B) : (term276 A B f) = (term276 A B f).
Proof. exact (MK_COMB (@lem3586196) (@lem3586195 A B f)). Qed.
Lemma lem3586198 {A B : Type'} (f : A -> B) : (term277 A B f) = (term278 A B f).
Proof. exact (MK_COMB (@lem3586197 A B f) (@lem3586192 A B f)). Qed.
Lemma lem3586199 {A B : Type'} (f : A -> B) : ((term225 A B f) = (term231 A B f)) = (term277 A B f).
Proof. exact (@lem17500 (term225 A B f) (term231 A B f)). Qed.
Lemma lem3586200 {A B : Type'} (f : A -> B) : ((term225 A B f) = (term231 A B f)) = (term278 A B f).
Proof. exact (TRANS (@lem3586199 A B f) (@lem3586198 A B f)). Qed.
Lemma lem3586235 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3586236 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (@lem3586235 A P Q). Qed.
Lemma lem3586237 {A B : Type'} (f : A -> B) : (term279 A B f) = (term280 A B f).
Proof. exact (@lem3586236 A (term224 A B f) (term231 A B f)). Qed.
Lemma lem3586238 {A B : Type'} (f : A -> B) (x : A) : (term255 A B f x) = (term222 A B f x).
Proof. exact (eq_refl (term255 A B f x)). Qed.
Lemma lem3586239 {A B : Type'} (f : A -> B) : (term281 A B f) = (term224 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586238 A B f x)). Qed.
Lemma lem3586240 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586241 {A B : Type'} (f : A -> B) : (term282 A B f) = (term225 A B f).
Proof. exact (MK_COMB (@lem3586240 A) (@lem3586239 A B f)). Qed.
Lemma lem3586242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586243 {A B : Type'} (f : A -> B) : (term283 A B f) = (term274 A B f).
Proof. exact (MK_COMB (@lem3586242) (@lem3586241 A B f)). Qed.
Lemma lem3586244 {A B : Type'} (f : A -> B) : (term231 A B f) = (term231 A B f).
Proof. exact (eq_refl (term231 A B f)). Qed.
Lemma lem3586245 {A B : Type'} (f : A -> B) : (term279 A B f) = (term275 A B f).
Proof. exact (MK_COMB (@lem3586243 A B f) (@lem3586244 A B f)). Qed.
Lemma lem3586246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586247 {A B : Type'} (f : A -> B) : (term284 A B f) = (term285 A B f).
Proof. exact (MK_COMB (@lem3586246) (@lem3586245 A B f)). Qed.
Lemma lem3586248 {A B : Type'} (f : A -> B) (x : A) : (term255 A B f x) = (term222 A B f x).
Proof. exact (eq_refl (term255 A B f x)). Qed.
Lemma lem3586249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586250 {A B : Type'} (f : A -> B) (x : A) : (term286 A B f x) = (term287 A B f x).
Proof. exact (MK_COMB (@lem3586249) (@lem3586248 A B f x)). Qed.
Lemma lem3586251 {A B : Type'} (f : A -> B) : (term231 A B f) = (term231 A B f).
Proof. exact (eq_refl (term231 A B f)). Qed.
Lemma lem3586252 {A B : Type'} (x : A) (f : A -> B) : (term288 A B x f) = (term289 A B x f).
Proof. exact (MK_COMB (@lem3586250 A B f x) (@lem3586251 A B f)). Qed.
Lemma lem3586253 {A B : Type'} (f : A -> B) : (term290 A B f) = (term291 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586252 A B x f)). Qed.
Lemma lem3586254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586255 {A B : Type'} (f : A -> B) : (term280 A B f) = (term292 A B f).
Proof. exact (MK_COMB (@lem3586254 A) (@lem3586253 A B f)). Qed.
Lemma lem3586256 {A B : Type'} (f : A -> B) : ((term279 A B f) = (term280 A B f)) = ((term275 A B f) = (term292 A B f)).
Proof. exact (MK_COMB (@lem3586247 A B f) (@lem3586255 A B f)). Qed.
Lemma lem3586257 {A B : Type'} (f : A -> B) : (term275 A B f) = (term292 A B f).
Proof. exact (EQ_MP (@lem3586256 A B f) (@lem3586237 A B f)). Qed.
Lemma lem3586259 {A : Type'} (P : Prop) (Q : A -> Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3586260 {B : Type'} (P : Prop) (Q : B -> Prop) : (term98 B P Q) = (term99 B P Q).
Proof. exact (@lem3586259 B P Q). Qed.
Lemma lem3586261 {A B : Type'} (x : A) (f : A -> B) : (term293 A B x f) = (term294 A B x f).
Proof. exact (@lem3586260 B (term222 A B f x) (term207 A B f)). Qed.
Lemma lem3586262 {A B : Type'} (f : A -> B) (y : B) : (term228 A B f y) = (term229 A B f y).
Proof. exact (eq_refl (term228 A B f y)). Qed.
Lemma lem3586263 {A B : Type'} (f : A -> B) : (term230 A B f) = (term207 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586262 A B f y)). Qed.
Lemma lem3586264 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586265 {A B : Type'} (f : A -> B) : (term209 A B f) = (term231 A B f).
Proof. exact (MK_COMB (@lem3586264 B) (@lem3586263 A B f)). Qed.
Lemma lem3586266 {A B : Type'} (f : A -> B) (x : A) : (term287 A B f x) = (term287 A B f x).
Proof. exact (eq_refl (term287 A B f x)). Qed.
Lemma lem3586267 {A B : Type'} (x : A) (f : A -> B) : (term293 A B x f) = (term289 A B x f).
Proof. exact (MK_COMB (@lem3586266 A B f x) (@lem3586265 A B f)). Qed.
Lemma lem3586268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586269 {A B : Type'} (x : A) (f : A -> B) : (term295 A B x f) = (term296 A B x f).
Proof. exact (MK_COMB (@lem3586268) (@lem3586267 A B x f)). Qed.
Lemma lem3586270 {A B : Type'} (f : A -> B) (y : B) : (term228 A B f y) = (term229 A B f y).
Proof. exact (eq_refl (term228 A B f y)). Qed.
Lemma lem3586271 {A B : Type'} (f : A -> B) (x : A) : (term287 A B f x) = (term287 A B f x).
Proof. exact (eq_refl (term287 A B f x)). Qed.
Lemma lem3586272 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term297 A B x f y) = (term298 A B x f y).
Proof. exact (MK_COMB (@lem3586271 A B f x) (@lem3586270 A B f y)). Qed.
Lemma lem3586273 {A B : Type'} (x : A) (f : A -> B) : (term299 A B x f) = (term300 A B x f).
Proof. exact (fun_ext (fun y : B => @lem3586272 A B x f y)). Qed.
Lemma lem3586274 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586275 {A B : Type'} (x : A) (f : A -> B) : (term294 A B x f) = (term301 A B x f).
Proof. exact (MK_COMB (@lem3586274 B) (@lem3586273 A B x f)). Qed.
Lemma lem3586276 {A B : Type'} (x : A) (f : A -> B) : ((term293 A B x f) = (term294 A B x f)) = ((term289 A B x f) = (term301 A B x f)).
Proof. exact (MK_COMB (@lem3586269 A B x f) (@lem3586275 A B x f)). Qed.
Lemma lem3586277 {A B : Type'} (x : A) (f : A -> B) : (term289 A B x f) = (term301 A B x f).
Proof. exact (EQ_MP (@lem3586276 A B x f) (@lem3586261 A B x f)). Qed.
Lemma lem3586278 {A B : Type'} (f : A -> B) : (term291 A B f) = (term302 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586277 A B x f)). Qed.
Lemma lem3586279 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586280 {A B : Type'} (f : A -> B) : (term292 A B f) = (term303 A B f).
Proof. exact (MK_COMB (@lem3586279 A) (@lem3586278 A B f)). Qed.
Lemma lem3586281 {A B : Type'} (f : A -> B) : (term275 A B f) = (term303 A B f).
Proof. exact (TRANS (@lem3586257 A B f) (@lem3586280 A B f)). Qed.
Lemma lem3586282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586283 {A B : Type'} (f : A -> B) : (term276 A B f) = (term304 A B f).
Proof. exact (MK_COMB (@lem3586282) (@lem3586281 A B f)). Qed.
Lemma lem3586285 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3586286 {A : Type'} (P : type1402 A) : (term305 A P) = (term306 A P).
Proof. exact (@lem3586285 A A P). Qed.
Lemma lem3586287 {A B : Type'} (f : A -> B) : (term307 A B f) = (term308 A B f).
Proof. exact (@lem3586286 A (term309 A B f)). Qed.
Lemma lem3586288 {A B : Type'} (f : A -> B) (x : A) : (term310 A B f x) = (term251 A B f x).
Proof. exact (eq_refl (term310 A B f x)). Qed.
Lemma lem3586289 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3586290 {A B : Type'} (f : A -> B) (x : A) (x' : A) : (term311 A B f x x') = (term312 A B f x x').
Proof. exact (MK_COMB (@lem3586288 A B f x) (@lem3586289 A x')). Qed.
Lemma lem3586291 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term312 A B f x x') = ((f x') = (f x)).
Proof. exact (eq_refl (term312 A B f x x')). Qed.
Lemma lem3586292 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term311 A B f x x') = ((f x') = (f x)).
Proof. exact (TRANS (@lem3586290 A B f x x') (@lem3586291 A B x' f x)). Qed.
Lemma lem3586293 {A B : Type'} (f : A -> B) (x : A) : (term313 A B f x) = (term251 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3586292 A B x' f x)). Qed.
Lemma lem3586294 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586295 {A B : Type'} (f : A -> B) (x : A) : (term314 A B f x) = (term252 A B f x).
Proof. exact (MK_COMB (@lem3586294 A) (@lem3586293 A B f x)). Qed.
Lemma lem3586296 {A B : Type'} (f : A -> B) : (term315 A B f) = (term258 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586295 A B f x)). Qed.
Lemma lem3586297 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586298 {A B : Type'} (f : A -> B) : (term307 A B f) = (term259 A B f).
Proof. exact (MK_COMB (@lem3586297 A) (@lem3586296 A B f)). Qed.
Lemma lem3586299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586300 {A B : Type'} (f : A -> B) : (term316 A B f) = (term317 A B f).
Proof. exact (MK_COMB (@lem3586299) (@lem3586298 A B f)). Qed.
Lemma lem3586301 {A B : Type'} (f : A -> B) (x : A) : (term310 A B f x) = (term251 A B f x).
Proof. exact (eq_refl (term310 A B f x)). Qed.
Lemma lem3586302 {A : Type'} (x' : A -> A) (x : A) : (x' x) = (x' x).
Proof. exact (eq_refl (x' x)). Qed.
Lemma lem3586303 {A B : Type'} (f : A -> B) (x' : A -> A) (x : A) : (term318 A B f x' x) = (term319 A B f x' x).
Proof. exact (MK_COMB (@lem3586301 A B f x) (@lem3586302 A x' x)). Qed.
Lemma lem3586304 {A B : Type'} (x' : A -> A) (f : A -> B) (x : A) : (term319 A B f x' x) = ((term320 A B f x' x) = (f x)).
Proof. exact (eq_refl (term319 A B f x' x)). Qed.
Lemma lem3586305 {A B : Type'} (x' : A -> A) (f : A -> B) (x : A) : (term318 A B f x' x) = ((term320 A B f x' x) = (f x)).
Proof. exact (TRANS (@lem3586303 A B f x' x) (@lem3586304 A B x' f x)). Qed.
Lemma lem3586306 {A B : Type'} (x' : A -> A) (f : A -> B) : (term321 A B f x') = (term322 A B x' f).
Proof. exact (fun_ext (fun x : A => @lem3586305 A B x' f x)). Qed.
Lemma lem3586307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586308 {A B : Type'} (x' : A -> A) (f : A -> B) : (term323 A B f x') = (term324 A B x' f).
Proof. exact (MK_COMB (@lem3586307 A) (@lem3586306 A B x' f)). Qed.
Lemma lem3586309 {A B : Type'} (f : A -> B) : (term325 A B f) = (term326 A B f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586308 A B x' f)). Qed.
Lemma lem3586310 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586311 {A B : Type'} (f : A -> B) : (term308 A B f) = (term327 A B f).
Proof. exact (MK_COMB (@lem3586310 A) (@lem3586309 A B f)). Qed.
Lemma lem3586312 {A B : Type'} (f : A -> B) : ((term307 A B f) = (term308 A B f)) = ((term259 A B f) = (term327 A B f)).
Proof. exact (MK_COMB (@lem3586300 A B f) (@lem3586311 A B f)). Qed.
Lemma lem3586313 {A B : Type'} (f : A -> B) : (term259 A B f) = (term327 A B f).
Proof. exact (EQ_MP (@lem3586312 A B f) (@lem3586287 A B f)). Qed.
Lemma lem3586314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586315 {A B : Type'} (f : A -> B) : (term271 A B f) = (term328 A B f).
Proof. exact (MK_COMB (@lem3586314) (@lem3586313 A B f)). Qed.
Lemma lem3586317 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3586318 {A B : Type'} (P : type1470 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (@lem3586317 B A P). Qed.
Lemma lem3586319 {A B : Type'} (f : A -> B) : (term32 A B f) = (term33 A B f).
Proof. exact (@lem3586318 A B (term34 A B f)). Qed.
Lemma lem3586320 {A B : Type'} (f : A -> B) (y : B) : (term35 A B f y) = (term21 A B f y).
Proof. exact (eq_refl (term35 A B f y)). Qed.
Lemma lem3586321 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3586322 {A B : Type'} (f : A -> B) (y : B) (x : A) : (term36 A B f y x) = (term37 A B f y x).
Proof. exact (MK_COMB (@lem3586320 A B f y) (@lem3586321 A x)). Qed.
Lemma lem3586323 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term37 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term37 A B f y x)). Qed.
Lemma lem3586324 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term36 A B f y x) = ((f x) = y).
Proof. exact (TRANS (@lem3586322 A B f y x) (@lem3586323 A B f x y)). Qed.
Lemma lem3586325 {A B : Type'} (f : A -> B) (y : B) : (term38 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586324 A B f x y)). Qed.
Lemma lem3586326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586327 {A B : Type'} (f : A -> B) (y : B) : (term39 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3586326 A) (@lem3586325 A B f y)). Qed.
Lemma lem3586328 {A B : Type'} (f : A -> B) : (term40 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3586327 A B f y)). Qed.
Lemma lem3586329 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586330 {A B : Type'} (f : A -> B) : (term32 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3586329 B) (@lem3586328 A B f)). Qed.
Lemma lem3586331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586332 {A B : Type'} (f : A -> B) : (term41 A B f) = (term42 A B f).
Proof. exact (MK_COMB (@lem3586331) (@lem3586330 A B f)). Qed.
Lemma lem3586333 {A B : Type'} (f : A -> B) (y : B) : (term35 A B f y) = (term21 A B f y).
Proof. exact (eq_refl (term35 A B f y)). Qed.
Lemma lem3586334 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3586335 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term43 A B f x y) = (term44 A B f x y).
Proof. exact (MK_COMB (@lem3586333 A B f y) (@lem3586334 A B x y)). Qed.
Lemma lem3586336 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term44 A B f x y) = ((term45 A B f x y) = y).
Proof. exact (eq_refl (term44 A B f x y)). Qed.
Lemma lem3586337 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term43 A B f x y) = ((term45 A B f x y) = y).
Proof. exact (TRANS (@lem3586335 A B f x y) (@lem3586336 A B f x y)). Qed.
Lemma lem3586338 {A B : Type'} (f : A -> B) (x : B -> A) : (term46 A B f x) = (term47 A B f x).
Proof. exact (fun_ext (fun y : B => @lem3586337 A B f x y)). Qed.
Lemma lem3586339 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586340 {A B : Type'} (f : A -> B) (x : B -> A) : (term48 A B f x) = (term49 A B f x).
Proof. exact (MK_COMB (@lem3586339 B) (@lem3586338 A B f x)). Qed.
Lemma lem3586341 {A B : Type'} (f : A -> B) : (term50 A B f) = (term51 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem3586340 A B f x)). Qed.
Lemma lem3586342 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3586343 {A B : Type'} (f : A -> B) : (term33 A B f) = (term52 A B f).
Proof. exact (MK_COMB (@lem3586342 A B) (@lem3586341 A B f)). Qed.
Lemma lem3586344 {A B : Type'} (f : A -> B) : ((term32 A B f) = (term33 A B f)) = ((term24 A B f) = (term52 A B f)).
Proof. exact (MK_COMB (@lem3586332 A B f) (@lem3586343 A B f)). Qed.
Lemma lem3586345 {A B : Type'} (f : A -> B) : (term24 A B f) = (term52 A B f).
Proof. exact (EQ_MP (@lem3586344 A B f) (@lem3586319 A B f)). Qed.
Lemma lem3586346 {A B : Type'} (f : A -> B) : (term273 A B f) = (term329 A B f).
Proof. exact (MK_COMB (@lem3586315 A B f) (@lem3586345 A B f)). Qed.
Lemma lem3586348 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3586349 {A : Type'} (P : type488 A) (Q : Prop) : (term330 A P Q) = (term331 A P Q).
Proof. exact (@lem3586348 (A -> A) P Q). Qed.
Lemma lem3586350 {A B : Type'} (f : A -> B) : (term332 A B f) = (term333 A B f).
Proof. exact (@lem3586349 A (term326 A B f) (term52 A B f)). Qed.
Lemma lem3586351 {A B : Type'} (x' : A -> A) (f : A -> B) : (term334 A B f x') = (term324 A B x' f).
Proof. exact (eq_refl (term334 A B f x')). Qed.
Lemma lem3586352 {A B : Type'} (f : A -> B) : (term335 A B f) = (term326 A B f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586351 A B x' f)). Qed.
Lemma lem3586353 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586354 {A B : Type'} (f : A -> B) : (term336 A B f) = (term327 A B f).
Proof. exact (MK_COMB (@lem3586353 A) (@lem3586352 A B f)). Qed.
Lemma lem3586355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586356 {A B : Type'} (f : A -> B) : (term337 A B f) = (term328 A B f).
Proof. exact (MK_COMB (@lem3586355) (@lem3586354 A B f)). Qed.
Lemma lem3586357 {A B : Type'} (f : A -> B) : (term52 A B f) = (term52 A B f).
Proof. exact (eq_refl (term52 A B f)). Qed.
Lemma lem3586358 {A B : Type'} (f : A -> B) : (term332 A B f) = (term329 A B f).
Proof. exact (MK_COMB (@lem3586356 A B f) (@lem3586357 A B f)). Qed.
Lemma lem3586359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586360 {A B : Type'} (f : A -> B) : (term338 A B f) = (term339 A B f).
Proof. exact (MK_COMB (@lem3586359) (@lem3586358 A B f)). Qed.
Lemma lem3586361 {A B : Type'} (x' : A -> A) (f : A -> B) : (term334 A B f x') = (term324 A B x' f).
Proof. exact (eq_refl (term334 A B f x')). Qed.
Lemma lem3586362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586363 {A B : Type'} (x' : A -> A) (f : A -> B) : (term340 A B f x') = (term341 A B x' f).
Proof. exact (MK_COMB (@lem3586362) (@lem3586361 A B x' f)). Qed.
Lemma lem3586364 {A B : Type'} (f : A -> B) : (term52 A B f) = (term52 A B f).
Proof. exact (eq_refl (term52 A B f)). Qed.
Lemma lem3586365 {A B : Type'} (x' : A -> A) (f : A -> B) : (term342 A B x' f) = (term343 A B x' f).
Proof. exact (MK_COMB (@lem3586363 A B x' f) (@lem3586364 A B f)). Qed.
Lemma lem3586366 {A B : Type'} (f : A -> B) : (term344 A B f) = (term345 A B f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586365 A B x' f)). Qed.
Lemma lem3586367 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586368 {A B : Type'} (f : A -> B) : (term333 A B f) = (term346 A B f).
Proof. exact (MK_COMB (@lem3586367 A) (@lem3586366 A B f)). Qed.
Lemma lem3586369 {A B : Type'} (f : A -> B) : ((term332 A B f) = (term333 A B f)) = ((term329 A B f) = (term346 A B f)).
Proof. exact (MK_COMB (@lem3586360 A B f) (@lem3586368 A B f)). Qed.
Lemma lem3586370 {A B : Type'} (f : A -> B) : (term329 A B f) = (term346 A B f).
Proof. exact (EQ_MP (@lem3586369 A B f) (@lem3586350 A B f)). Qed.
Lemma lem3586372 {A : Type'} (P : Prop) (Q : A -> Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3586373 {A B : Type'} (P : Prop) (Q : type805 A B) : (term347 A B P Q) = (term348 A B P Q).
Proof. exact (@lem3586372 (B -> A) P Q). Qed.
Lemma lem3586374 {A B : Type'} (x' : A -> A) (f : A -> B) : (term349 A B x' f) = (term350 A B x' f).
Proof. exact (@lem3586373 A B (term324 A B x' f) (term51 A B f)). Qed.
Lemma lem3586375 {A B : Type'} (f : A -> B) (x : B -> A) : (term351 A B f x) = (term49 A B f x).
Proof. exact (eq_refl (term351 A B f x)). Qed.
Lemma lem3586376 {A B : Type'} (f : A -> B) : (term352 A B f) = (term51 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem3586375 A B f x)). Qed.
Lemma lem3586377 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3586378 {A B : Type'} (f : A -> B) : (term353 A B f) = (term52 A B f).
Proof. exact (MK_COMB (@lem3586377 A B) (@lem3586376 A B f)). Qed.
Lemma lem3586379 {A B : Type'} (x' : A -> A) (f : A -> B) : (term341 A B x' f) = (term341 A B x' f).
Proof. exact (eq_refl (term341 A B x' f)). Qed.
Lemma lem3586380 {A B : Type'} (x' : A -> A) (f : A -> B) : (term349 A B x' f) = (term343 A B x' f).
Proof. exact (MK_COMB (@lem3586379 A B x' f) (@lem3586378 A B f)). Qed.
Lemma lem3586381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586382 {A B : Type'} (x' : A -> A) (f : A -> B) : (term354 A B x' f) = (term355 A B x' f).
Proof. exact (MK_COMB (@lem3586381) (@lem3586380 A B x' f)). Qed.
Lemma lem3586383 {A B : Type'} (f : A -> B) (x : B -> A) : (term351 A B f x) = (term49 A B f x).
Proof. exact (eq_refl (term351 A B f x)). Qed.
Lemma lem3586384 {A B : Type'} (x' : A -> A) (f : A -> B) : (term341 A B x' f) = (term341 A B x' f).
Proof. exact (eq_refl (term341 A B x' f)). Qed.
Lemma lem3586385 {A B : Type'} (x' : A -> A) (f : A -> B) (x : B -> A) : (term356 A B x' f x) = (term357 A B x' f x).
Proof. exact (MK_COMB (@lem3586384 A B x' f) (@lem3586383 A B f x)). Qed.
Lemma lem3586386 {A B : Type'} (x' : A -> A) (f : A -> B) : (term358 A B x' f) = (term359 A B x' f).
Proof. exact (fun_ext (fun x : B -> A => @lem3586385 A B x' f x)). Qed.
Lemma lem3586387 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3586388 {A B : Type'} (x' : A -> A) (f : A -> B) : (term350 A B x' f) = (term360 A B x' f).
Proof. exact (MK_COMB (@lem3586387 A B) (@lem3586386 A B x' f)). Qed.
Lemma lem3586389 {A B : Type'} (x' : A -> A) (f : A -> B) : ((term349 A B x' f) = (term350 A B x' f)) = ((term343 A B x' f) = (term360 A B x' f)).
Proof. exact (MK_COMB (@lem3586382 A B x' f) (@lem3586388 A B x' f)). Qed.
Lemma lem3586390 {A B : Type'} (x' : A -> A) (f : A -> B) : (term343 A B x' f) = (term360 A B x' f).
Proof. exact (EQ_MP (@lem3586389 A B x' f) (@lem3586374 A B x' f)). Qed.
Lemma lem3586391 {A B : Type'} (f : A -> B) : (term345 A B f) = (term361 A B f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586390 A B x' f)). Qed.
Lemma lem3586392 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586393 {A B : Type'} (f : A -> B) : (term346 A B f) = (term362 A B f).
Proof. exact (MK_COMB (@lem3586392 A) (@lem3586391 A B f)). Qed.
Lemma lem3586394 {A B : Type'} (f : A -> B) : (term329 A B f) = (term362 A B f).
Proof. exact (TRANS (@lem3586370 A B f) (@lem3586393 A B f)). Qed.
Lemma lem3586395 {A B : Type'} (f : A -> B) : (term273 A B f) = (term362 A B f).
Proof. exact (TRANS (@lem3586346 A B f) (@lem3586394 A B f)). Qed.
Lemma lem3586396 {A B : Type'} (f : A -> B) : (term278 A B f) = (term363 A B f).
Proof. exact (MK_COMB (@lem3586283 A B f) (@lem3586395 A B f)). Qed.
Lemma lem3586400 {A : Type'} (P : A -> Prop) (Q : Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3586401 {A : Type'} (P : A -> Prop) (Q : Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (@lem3586400 A P Q). Qed.
Lemma lem3586402 {A B : Type'} (f : A -> B) : (term364 A B f) = (term365 A B f).
Proof. exact (@lem3586401 A (term302 A B f) (term362 A B f)). Qed.
Lemma lem3586403 {A B : Type'} (x : A) (f : A -> B) : (term366 A B f x) = (term301 A B x f).
Proof. exact (eq_refl (term366 A B f x)). Qed.
Lemma lem3586404 {A B : Type'} (f : A -> B) : (term367 A B f) = (term302 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586403 A B x f)). Qed.
Lemma lem3586405 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586406 {A B : Type'} (f : A -> B) : (term368 A B f) = (term303 A B f).
Proof. exact (MK_COMB (@lem3586405 A) (@lem3586404 A B f)). Qed.
Lemma lem3586407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586408 {A B : Type'} (f : A -> B) : (term369 A B f) = (term304 A B f).
Proof. exact (MK_COMB (@lem3586407) (@lem3586406 A B f)). Qed.
Lemma lem3586409 {A B : Type'} (f : A -> B) : (term362 A B f) = (term362 A B f).
Proof. exact (eq_refl (term362 A B f)). Qed.
Lemma lem3586410 {A B : Type'} (f : A -> B) : (term364 A B f) = (term363 A B f).
Proof. exact (MK_COMB (@lem3586408 A B f) (@lem3586409 A B f)). Qed.
Lemma lem3586411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586412 {A B : Type'} (f : A -> B) : (term370 A B f) = (term371 A B f).
Proof. exact (MK_COMB (@lem3586411) (@lem3586410 A B f)). Qed.
Lemma lem3586413 {A B : Type'} (x : A) (f : A -> B) : (term366 A B f x) = (term301 A B x f).
Proof. exact (eq_refl (term366 A B f x)). Qed.
Lemma lem3586414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586415 {A B : Type'} (x : A) (f : A -> B) : (term372 A B f x) = (term373 A B x f).
Proof. exact (MK_COMB (@lem3586414) (@lem3586413 A B x f)). Qed.
Lemma lem3586416 {A B : Type'} (f : A -> B) : (term362 A B f) = (term362 A B f).
Proof. exact (eq_refl (term362 A B f)). Qed.
Lemma lem3586417 {A B : Type'} (x : A) (f : A -> B) : (term374 A B x f) = (term375 A B x f).
Proof. exact (MK_COMB (@lem3586415 A B x f) (@lem3586416 A B f)). Qed.
Lemma lem3586418 {A B : Type'} (f : A -> B) : (term376 A B f) = (term377 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586417 A B x f)). Qed.
Lemma lem3586419 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586420 {A B : Type'} (f : A -> B) : (term365 A B f) = (term378 A B f).
Proof. exact (MK_COMB (@lem3586419 A) (@lem3586418 A B f)). Qed.
Lemma lem3586421 {A B : Type'} (f : A -> B) : ((term364 A B f) = (term365 A B f)) = ((term363 A B f) = (term378 A B f)).
Proof. exact (MK_COMB (@lem3586412 A B f) (@lem3586420 A B f)). Qed.
Lemma lem3586422 {A B : Type'} (f : A -> B) : (term363 A B f) = (term378 A B f).
Proof. exact (EQ_MP (@lem3586421 A B f) (@lem3586402 A B f)). Qed.
Lemma lem3586426 {A : Type'} (P : A -> Prop) (Q : Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3586427 {B : Type'} (P : B -> Prop) (Q : Prop) : (term102 B P Q) = (term103 B P Q).
Proof. exact (@lem3586426 B P Q). Qed.
Lemma lem3586428 {A B : Type'} (x : A) (f : A -> B) : (term379 A B x f) = (term380 A B x f).
Proof. exact (@lem3586427 B (term300 A B x f) (term362 A B f)). Qed.
Lemma lem3586429 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term381 A B x f y) = (term298 A B x f y).
Proof. exact (eq_refl (term381 A B x f y)). Qed.
Lemma lem3586430 {A B : Type'} (x : A) (f : A -> B) : (term382 A B x f) = (term300 A B x f).
Proof. exact (fun_ext (fun y : B => @lem3586429 A B x f y)). Qed.
Lemma lem3586431 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586432 {A B : Type'} (x : A) (f : A -> B) : (term383 A B x f) = (term301 A B x f).
Proof. exact (MK_COMB (@lem3586431 B) (@lem3586430 A B x f)). Qed.
Lemma lem3586433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586434 {A B : Type'} (x : A) (f : A -> B) : (term384 A B x f) = (term373 A B x f).
Proof. exact (MK_COMB (@lem3586433) (@lem3586432 A B x f)). Qed.
Lemma lem3586435 {A B : Type'} (f : A -> B) : (term362 A B f) = (term362 A B f).
Proof. exact (eq_refl (term362 A B f)). Qed.
Lemma lem3586436 {A B : Type'} (x : A) (f : A -> B) : (term379 A B x f) = (term375 A B x f).
Proof. exact (MK_COMB (@lem3586434 A B x f) (@lem3586435 A B f)). Qed.
Lemma lem3586437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586438 {A B : Type'} (x : A) (f : A -> B) : (term385 A B x f) = (term386 A B x f).
Proof. exact (MK_COMB (@lem3586437) (@lem3586436 A B x f)). Qed.
Lemma lem3586439 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term381 A B x f y) = (term298 A B x f y).
Proof. exact (eq_refl (term381 A B x f y)). Qed.
Lemma lem3586440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586441 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term387 A B x f y) = (term388 A B x f y).
Proof. exact (MK_COMB (@lem3586440) (@lem3586439 A B x f y)). Qed.
Lemma lem3586442 {A B : Type'} (f : A -> B) : (term362 A B f) = (term362 A B f).
Proof. exact (eq_refl (term362 A B f)). Qed.
Lemma lem3586443 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term389 A B x y f) = (term390 A B x y f).
Proof. exact (MK_COMB (@lem3586441 A B x f y) (@lem3586442 A B f)). Qed.
Lemma lem3586444 {A B : Type'} (x : A) (f : A -> B) : (term391 A B x f) = (term392 A B x f).
Proof. exact (fun_ext (fun y : B => @lem3586443 A B x y f)). Qed.
Lemma lem3586445 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586446 {A B : Type'} (x : A) (f : A -> B) : (term380 A B x f) = (term393 A B x f).
Proof. exact (MK_COMB (@lem3586445 B) (@lem3586444 A B x f)). Qed.
Lemma lem3586447 {A B : Type'} (x : A) (f : A -> B) : ((term379 A B x f) = (term380 A B x f)) = ((term375 A B x f) = (term393 A B x f)).
Proof. exact (MK_COMB (@lem3586438 A B x f) (@lem3586446 A B x f)). Qed.
Lemma lem3586448 {A B : Type'} (x : A) (f : A -> B) : (term375 A B x f) = (term393 A B x f).
Proof. exact (EQ_MP (@lem3586447 A B x f) (@lem3586428 A B x f)). Qed.
Lemma lem3586450 {A : Type'} (P : Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3586451 {A : Type'} (P : Prop) (Q : type488 A) : (term394 A P Q) = (term395 A P Q).
Proof. exact (@lem3586450 (A -> A) P Q). Qed.
Lemma lem3586452 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term396 A B x y f) = (term397 A B x y f).
Proof. exact (@lem3586451 A (term298 A B x f y) (term361 A B f)). Qed.
Lemma lem3586453 {A B : Type'} (x' : A -> A) (f : A -> B) : (term398 A B f x') = (term360 A B x' f).
Proof. exact (eq_refl (term398 A B f x')). Qed.
Lemma lem3586454 {A B : Type'} (f : A -> B) : (term399 A B f) = (term361 A B f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586453 A B x' f)). Qed.
Lemma lem3586455 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586456 {A B : Type'} (f : A -> B) : (term400 A B f) = (term362 A B f).
Proof. exact (MK_COMB (@lem3586455 A) (@lem3586454 A B f)). Qed.
Lemma lem3586457 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term388 A B x f y) = (term388 A B x f y).
Proof. exact (eq_refl (term388 A B x f y)). Qed.
Lemma lem3586458 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term396 A B x y f) = (term390 A B x y f).
Proof. exact (MK_COMB (@lem3586457 A B x f y) (@lem3586456 A B f)). Qed.
Lemma lem3586459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586460 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term401 A B x y f) = (term402 A B x y f).
Proof. exact (MK_COMB (@lem3586459) (@lem3586458 A B x y f)). Qed.
Lemma lem3586461 {A B : Type'} (x' : A -> A) (f : A -> B) : (term398 A B f x') = (term360 A B x' f).
Proof. exact (eq_refl (term398 A B f x')). Qed.
Lemma lem3586462 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term388 A B x f y) = (term388 A B x f y).
Proof. exact (eq_refl (term388 A B x f y)). Qed.
Lemma lem3586463 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term403 A B x y f x') = (term404 A B x y x' f).
Proof. exact (MK_COMB (@lem3586462 A B x f y) (@lem3586461 A B x' f)). Qed.
Lemma lem3586464 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term405 A B x y f) = (term406 A B x y f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586463 A B x y x' f)). Qed.
Lemma lem3586465 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586466 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term397 A B x y f) = (term407 A B x y f).
Proof. exact (MK_COMB (@lem3586465 A) (@lem3586464 A B x y f)). Qed.
Lemma lem3586467 {A B : Type'} (x : A) (y : B) (f : A -> B) : ((term396 A B x y f) = (term397 A B x y f)) = ((term390 A B x y f) = (term407 A B x y f)).
Proof. exact (MK_COMB (@lem3586460 A B x y f) (@lem3586466 A B x y f)). Qed.
Lemma lem3586468 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term390 A B x y f) = (term407 A B x y f).
Proof. exact (EQ_MP (@lem3586467 A B x y f) (@lem3586452 A B x y f)). Qed.
Lemma lem3586470 {A : Type'} (P : Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3586471 {A B : Type'} (P : Prop) (Q : type805 A B) : (term408 A B P Q) = (term409 A B P Q).
Proof. exact (@lem3586470 (B -> A) P Q). Qed.
Lemma lem3586472 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term410 A B x y x' f) = (term411 A B x y x' f).
Proof. exact (@lem3586471 A B (term298 A B x f y) (term359 A B x' f)). Qed.
Lemma lem3586473 {A B : Type'} (x' : A -> A) (f : A -> B) (x : B -> A) : (term412 A B x' f x) = (term357 A B x' f x).
Proof. exact (eq_refl (term412 A B x' f x)). Qed.
Lemma lem3586474 {A B : Type'} (x' : A -> A) (f : A -> B) : (term413 A B x' f) = (term359 A B x' f).
Proof. exact (fun_ext (fun x : B -> A => @lem3586473 A B x' f x)). Qed.
Lemma lem3586475 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3586476 {A B : Type'} (x' : A -> A) (f : A -> B) : (term414 A B x' f) = (term360 A B x' f).
Proof. exact (MK_COMB (@lem3586475 A B) (@lem3586474 A B x' f)). Qed.
Lemma lem3586477 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term388 A B x f y) = (term388 A B x f y).
Proof. exact (eq_refl (term388 A B x f y)). Qed.
Lemma lem3586478 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term410 A B x y x' f) = (term404 A B x y x' f).
Proof. exact (MK_COMB (@lem3586477 A B x f y) (@lem3586476 A B x' f)). Qed.
Lemma lem3586479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586480 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term415 A B x y x' f) = (term416 A B x y x' f).
Proof. exact (MK_COMB (@lem3586479) (@lem3586478 A B x y x' f)). Qed.
Lemma lem3586481 {A B : Type'} (x' : A -> A) (f : A -> B) (x : B -> A) : (term412 A B x' f x) = (term357 A B x' f x).
Proof. exact (eq_refl (term412 A B x' f x)). Qed.
Lemma lem3586482 {A B : Type'} (x : A) (f : A -> B) (y : B) : (term388 A B x f y) = (term388 A B x f y).
Proof. exact (eq_refl (term388 A B x f y)). Qed.
Lemma lem3586483 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) : (term417 A B x y x' f x'') = (term418 A B x y x' f x'').
Proof. exact (MK_COMB (@lem3586482 A B x f y) (@lem3586481 A B x' f x'')). Qed.
Lemma lem3586484 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term419 A B x y x' f) = (term420 A B x y x' f).
Proof. exact (fun_ext (fun x'' : B -> A => @lem3586483 A B x y x' f x'')). Qed.
Lemma lem3586485 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3586486 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term411 A B x y x' f) = (term421 A B x y x' f).
Proof. exact (MK_COMB (@lem3586485 A B) (@lem3586484 A B x y x' f)). Qed.
Lemma lem3586487 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : ((term410 A B x y x' f) = (term411 A B x y x' f)) = ((term404 A B x y x' f) = (term421 A B x y x' f)).
Proof. exact (MK_COMB (@lem3586480 A B x y x' f) (@lem3586486 A B x y x' f)). Qed.
Lemma lem3586488 {A B : Type'} (x : A) (y : B) (x' : A -> A) (f : A -> B) : (term404 A B x y x' f) = (term421 A B x y x' f).
Proof. exact (EQ_MP (@lem3586487 A B x y x' f) (@lem3586472 A B x y x' f)). Qed.
Lemma lem3586489 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term406 A B x y f) = (term422 A B x y f).
Proof. exact (fun_ext (fun x' : A -> A => @lem3586488 A B x y x' f)). Qed.
Lemma lem3586490 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3586491 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term407 A B x y f) = (term423 A B x y f).
Proof. exact (MK_COMB (@lem3586490 A) (@lem3586489 A B x y f)). Qed.
Lemma lem3586492 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term390 A B x y f) = (term423 A B x y f).
Proof. exact (TRANS (@lem3586468 A B x y f) (@lem3586491 A B x y f)). Qed.
Lemma lem3586493 {A B : Type'} (x : A) (f : A -> B) : (term392 A B x f) = (term424 A B x f).
Proof. exact (fun_ext (fun y : B => @lem3586492 A B x y f)). Qed.
Lemma lem3586494 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3586495 {A B : Type'} (x : A) (f : A -> B) : (term393 A B x f) = (term425 A B x f).
Proof. exact (MK_COMB (@lem3586494 B) (@lem3586493 A B x f)). Qed.
Lemma lem3586496 {A B : Type'} (x : A) (f : A -> B) : (term375 A B x f) = (term425 A B x f).
Proof. exact (TRANS (@lem3586448 A B x f) (@lem3586495 A B x f)). Qed.
Lemma lem3586497 {A B : Type'} (f : A -> B) : (term377 A B f) = (term426 A B f).
Proof. exact (fun_ext (fun x : A => @lem3586496 A B x f)). Qed.
Lemma lem3586498 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586499 {A B : Type'} (f : A -> B) : (term378 A B f) = (term427 A B f).
Proof. exact (MK_COMB (@lem3586498 A) (@lem3586497 A B f)). Qed.
Lemma lem3586500 {A B : Type'} (f : A -> B) : (term363 A B f) = (term427 A B f).
Proof. exact (TRANS (@lem3586422 A B f) (@lem3586499 A B f)). Qed.
Lemma lem3586502 {A B : Type'} (f : A -> B) : (term278 A B f) = (term427 A B f).
Proof. exact (TRANS (@lem3586396 A B f) (@lem3586500 A B f)). Qed.
Lemma lem3586503 {A B : Type'} (f : A -> B) : ((term225 A B f) = (term231 A B f)) = (term427 A B f).
Proof. exact (TRANS (@lem3586200 A B f) (@lem3586502 A B f)). Qed.
Lemma lem3586504 {A B : Type'} (f : A -> B) (h1 : (term225 A B f) = (term231 A B f)) : term427 A B f.
Proof. exact (EQ_MP (@lem3586503 A B f) (@lem3586124 A B f h1)). Qed.
Lemma lem3586506 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3586507 {A B : Type'} (f : A -> B) (y : B) : (term242 A B f y) = (term428 A B f y).
Proof. exact (@lem3586506 A (term21 A B f y)). Qed.
Lemma lem3586508 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term37 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term37 A B f y x)). Qed.
Lemma lem3586509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3586511 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term429 A B f y x) = (term237 A B f x y).
Proof. exact (MK_COMB (@lem3586509) (@lem3586508 A B f x y)). Qed.
Lemma lem3586512 {A B : Type'} (f : A -> B) (y : B) : (term430 A B f y) = (term238 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586511 A B f x y)). Qed.
Lemma lem3586513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586514 {A B : Type'} (f : A -> B) (y : B) : (term428 A B f y) = (term229 A B f y).
Proof. exact (MK_COMB (@lem3586513 A) (@lem3586512 A B f y)). Qed.
Lemma lem3586523 {A B : Type'} (f : A -> B) (y : B) : (term242 A B f y) = (term229 A B f y).
Proof. exact (TRANS (@lem3586507 A B f y) (@lem3586514 A B f y)). Qed.
Lemma lem3586524 {A B : Type'} (f : A -> B) (y : B) (h1 : term242 A B f y) : term229 A B f y.
Proof. exact (EQ_MP (@lem3586523 A B f y) (@lem3586129 A B f y h1)). Qed.
Lemma lem3586525 {A B : Type'} (x : A) (f : A -> B) (h1 : term425 A B x f) : term425 A B x f.
Proof. exact (h1). Qed.
Lemma lem3586526 {A B : Type'} (x : A) (y' : B) (f : A -> B) (h1 : term423 A B x y' f) : term423 A B x y' f.
Proof. exact (h1). Qed.
Lemma lem3586527 {A B : Type'} (x : A) (y' : B) (x' : A -> A) (f : A -> B) (h1 : term421 A B x y' x' f) : term421 A B x y' x' f.
Proof. exact (h1). Qed.
Lemma lem3586528 {A B : Type'} (x : A) (y' : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term418 A B x y' x' f x'') : term418 A B x y' x' f x''.
Proof. exact (h1). Qed.
Lemma lem3586537 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term237 A B f x y) = (term237 A B f x y).
Proof. exact (eq_refl (term237 A B f x y)). Qed.
Lemma lem3586538 {A B : Type'} (f : A -> B) (y : B) : (term238 A B f y) = (term238 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586537 A B f x y)). Qed.
Lemma lem3586539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586540 {A B : Type'} (f : A -> B) (y : B) : (term229 A B f y) = (term229 A B f y).
Proof. exact (MK_COMB (@lem3586539 A) (@lem3586538 A B f y)). Qed.
Lemma lem3586541 {A B : Type'} (f : A -> B) (y : B) (h1 : term242 A B f y) : term229 A B f y.
Proof. exact (EQ_MP (@lem3586540 A B f y) (@lem3586524 A B f y h1)). Qed.
Lemma lem3586550 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : ((term45 A B f x'' y) = y) = ((term45 A B f x'' y) = y).
Proof. exact (eq_refl ((term45 A B f x'' y) = y)). Qed.
Lemma lem3586551 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term47 A B f x'') = (term47 A B f x'').
Proof. exact (fun_ext (fun y : B => @lem3586550 A B f x'' y)). Qed.
Lemma lem3586552 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586553 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term49 A B f x'') = (term49 A B f x'').
Proof. exact (MK_COMB (@lem3586552 B) (@lem3586551 A B f x'')). Qed.
Lemma lem3586564 {A B : Type'} (x' : A -> A) (f : A -> B) (x : A) : ((term320 A B f x' x) = (f x)) = ((term320 A B f x' x) = (f x)).
Proof. exact (eq_refl ((term320 A B f x' x) = (f x))). Qed.
Lemma lem3586565 {A B : Type'} (x' : A -> A) (f : A -> B) : (term322 A B x' f) = (term322 A B x' f).
Proof. exact (fun_ext (fun x : A => @lem3586564 A B x' f x)). Qed.
Lemma lem3586566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586567 {A B : Type'} (x' : A -> A) (f : A -> B) : (term324 A B x' f) = (term324 A B x' f).
Proof. exact (MK_COMB (@lem3586566 A) (@lem3586565 A B x' f)). Qed.
Lemma lem3586568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586569 {A B : Type'} (x' : A -> A) (f : A -> B) : (term341 A B x' f) = (term341 A B x' f).
Proof. exact (MK_COMB (@lem3586568) (@lem3586567 A B x' f)). Qed.
Lemma lem3586570 {A B : Type'} (x' : A -> A) (f : A -> B) (x'' : B -> A) : (term357 A B x' f x'') = (term357 A B x' f x'').
Proof. exact (MK_COMB (@lem3586569 A B x' f) (@lem3586553 A B f x'')). Qed.
Lemma lem3586579 {A B : Type'} (f : A -> B) (x : A) (y' : B) : (term237 A B f x y') = (term237 A B f x y').
Proof. exact (eq_refl (term237 A B f x y')). Qed.
Lemma lem3586580 {A B : Type'} (f : A -> B) (y' : B) : (term238 A B f y') = (term238 A B f y').
Proof. exact (fun_ext (fun x : A => @lem3586579 A B f x y')). Qed.
Lemma lem3586581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586582 {A B : Type'} (f : A -> B) (y' : B) : (term229 A B f y') = (term229 A B f y').
Proof. exact (MK_COMB (@lem3586581 A) (@lem3586580 A B f y')). Qed.
Lemma lem3586593 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term239 A B x' f x) = (term239 A B x' f x).
Proof. exact (eq_refl (term239 A B x' f x)). Qed.
Lemma lem3586594 {A B : Type'} (f : A -> B) (x : A) : (term240 A B f x) = (term240 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3586593 A B x' f x)). Qed.
Lemma lem3586595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586596 {A B : Type'} (f : A -> B) (x : A) : (term222 A B f x) = (term222 A B f x).
Proof. exact (MK_COMB (@lem3586595 A) (@lem3586594 A B f x)). Qed.
Lemma lem3586597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3586598 {A B : Type'} (f : A -> B) (x : A) : (term287 A B f x) = (term287 A B f x).
Proof. exact (MK_COMB (@lem3586597) (@lem3586596 A B f x)). Qed.
Lemma lem3586599 {A B : Type'} (x : A) (f : A -> B) (y' : B) : (term298 A B x f y') = (term298 A B x f y').
Proof. exact (MK_COMB (@lem3586598 A B f x) (@lem3586582 A B f y')). Qed.
Lemma lem3586600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3586601 {A B : Type'} (x : A) (f : A -> B) (y' : B) : (term388 A B x f y') = (term388 A B x f y').
Proof. exact (MK_COMB (@lem3586600) (@lem3586599 A B x f y')). Qed.
Lemma lem3586602 {A B : Type'} (x : A) (y' : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) : (term418 A B x y' x' f x'') = (term418 A B x y' x' f x'').
Proof. exact (MK_COMB (@lem3586601 A B x f y') (@lem3586570 A B x' f x'')). Qed.
Lemma lem3586603 {A B : Type'} (x : A) (y' : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term418 A B x y' x' f x'') : term418 A B x y' x' f x''.
Proof. exact (EQ_MP (@lem3586602 A B x y' x' f x'') (@lem3586528 A B x y' x' f x'' h1)). Qed.
Lemma lem3586604 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term298 A B x f y'.
Proof. exact (h1). Qed.
Lemma lem3586605 {A B : Type'} (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : term357 A B x' f x''.
Proof. exact (h1). Qed.
Lemma lem3586607 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term222 A B f x.
Proof. exact (proj1 (@lem3586604 A B x f y' h1)). Qed.
Lemma lem3586608 {A B : Type'} (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : term49 A B f x''.
Proof. exact (proj2 (@lem3586605 A B x' f x'' h1)). Qed.
Lemma lem3586618 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term239 A B x' f x) = (term239 A B x' f x).
Proof. exact (eq_refl (term239 A B x' f x)). Qed.
Lemma lem3586619 {A B : Type'} (f : A -> B) (x : A) : (term240 A B f x) = (term240 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3586618 A B x' f x)). Qed.
Lemma lem3586620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586622 {A B : Type'} (f : A -> B) (x : A) : (term222 A B f x) = (term222 A B f x).
Proof. exact (MK_COMB (@lem3586620 A) (@lem3586619 A B f x)). Qed.
Lemma lem3586623 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term222 A B f x.
Proof. exact (EQ_MP (@lem3586622 A B f x) (@lem3586607 A B x f y' h1)). Qed.
Lemma lem3586632 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term237 A B f x y) = (term237 A B f x y).
Proof. exact (eq_refl (term237 A B f x y)). Qed.
Lemma lem3586633 {A B : Type'} (f : A -> B) (y : B) : (term238 A B f y) = (term238 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3586632 A B f x y)). Qed.
Lemma lem3586634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3586636 {A B : Type'} (f : A -> B) (y : B) : (term229 A B f y) = (term229 A B f y).
Proof. exact (MK_COMB (@lem3586634 A) (@lem3586633 A B f y)). Qed.
Lemma lem3586637 {A B : Type'} (f : A -> B) (y : B) (h1 : term242 A B f y) : term229 A B f y.
Proof. exact (EQ_MP (@lem3586636 A B f y) (@lem3586541 A B f y h1)). Qed.
Lemma lem3586646 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : ((term45 A B f x'' y) = y) = ((term45 A B f x'' y) = y).
Proof. exact (eq_refl ((term45 A B f x'' y) = y)). Qed.
Lemma lem3586647 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term47 A B f x'') = (term47 A B f x'').
Proof. exact (fun_ext (fun y : B => @lem3586646 A B f x'' y)). Qed.
Lemma lem3586648 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586650 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term49 A B f x'') = (term49 A B f x'').
Proof. exact (MK_COMB (@lem3586648 B) (@lem3586647 A B f x'')). Qed.
Lemma lem3586651 {A B : Type'} (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : term49 A B f x''.
Proof. exact (EQ_MP (@lem3586650 A B f x'') (@lem3586608 A B x' f x'' h1)). Qed.
Lemma lem3586655 {A B : Type'} (_38735 : A) (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term248 A B f x _38735.
Proof. exact (@lem3586623 A B x f y' h1 _38735). Qed.
Lemma lem3586656 {A B : Type'} (_38735 : A) (f : A -> B) (x : A) : (term248 A B f x _38735) = (term239 A B _38735 f x).
Proof. exact (eq_refl (term248 A B f x _38735)). Qed.
Lemma lem3586661 {A B : Type'} (_38737 : A) (f : A -> B) (y : B) (h1 : term242 A B f y) : term263 A B f y _38737.
Proof. exact (@lem3586637 A B f y h1 _38737). Qed.
Lemma lem3586662 {A B : Type'} (f : A -> B) (_38737 : A) (y : B) : (term263 A B f y _38737) = (term237 A B f _38737 y).
Proof. exact (eq_refl (term263 A B f y _38737)). Qed.
Lemma lem3586667 {A B : Type'} (_38739 : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : term138 A B f x'' _38739.
Proof. exact (@lem3586651 A B x' f x'' h1 _38739). Qed.
Lemma lem3586668 {A B : Type'} (f : A -> B) (x'' : B -> A) (_38739 : B) : (term138 A B f x'' _38739) = ((term45 A B f x'' _38739) = _38739).
Proof. exact (eq_refl (term138 A B f x'' _38739)). Qed.
Lemma lem3586673 {A B : Type'} (_38735 : A) (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term239 A B _38735 f x.
Proof. exact (EQ_MP (@lem3586656 A B _38735 f x) (@lem3586655 A B _38735 x f y' h1)). Qed.
Lemma lem3586677 {A B : Type'} (_38737 : A) (f : A -> B) (y : B) (h1 : term242 A B f y) : term237 A B f _38737 y.
Proof. exact (EQ_MP (@lem3586662 A B f _38737 y) (@lem3586661 A B _38737 f y h1)). Qed.
Lemma lem3586695 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3586696 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3586695 B x). Qed.
Lemma lem3586697 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3586696 B (f x)). Qed.
Lemma lem3586698 {A B : Type'} (f : A -> B) (x : A) : term431 A B f x.
Proof. exact (fun h0 : term432 A B f x => @lem3586697 A B f x). Qed.
Lemma lem3586700 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3586701 {A B : Type'} (f : A -> B) (x : A) : (term431 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3586700 ((f x) = (f x))). Qed.
Lemma lem3586702 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3586701 A B f x) (@lem3586698 A B f x)). Qed.
Lemma lem3586705 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3586707 {A B : Type'} (_38735 : A) (f : A -> B) (x : A) : (term239 A B _38735 f x) = (term433 A B _38735 f x).
Proof. exact (@lem3586705 ((f _38735) = (f x))). Qed.
Lemma lem3586710 {A B : Type'} (_38735 : A) (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term433 A B _38735 f x.
Proof. exact (EQ_MP (@lem3586707 A B _38735 f x) (@lem3586673 A B _38735 x f y' h1)). Qed.
Lemma lem3586711 {A B : Type'} (_38735 : A) (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term433 A B _38735 f x.
Proof. exact (@lem3586710 A B _38735 x f y' h1). Qed.
Lemma lem3586712 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term434 A B f x.
Proof. exact (@lem3586711 A B x x f y' h1). Qed.
Lemma lem3586715 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : False.
Proof. exact (@lem3586712 A B x f y' h1 (@lem3586702 A B f x)). Qed.
Lemma lem3586716 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : term144.
Proof. exact (fun h0 : ~ False => @lem3586715 A B x f y' h1). Qed.
Lemma lem3586718 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3586719 : term144 = False.
Proof. exact (@lem3586718 False). Qed.
Lemma lem3586720 {A B : Type'} (x : A) (f : A -> B) (y' : B) (h1 : term298 A B x f y') : False.
Proof. exact (EQ_MP (@lem3586719) (@lem3586716 A B x f y' h1)). Qed.
Lemma lem3586750 {A B : Type'} (_38739 : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : (term45 A B f x'' _38739) = _38739.
Proof. exact (EQ_MP (@lem3586668 A B f x'' _38739) (@lem3586667 A B _38739 x' f x'' h1)). Qed.
Lemma lem3586751 {A B : Type'} (_38739 : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : (term45 A B f x'' _38739) = _38739.
Proof. exact (@lem3586750 A B _38739 x' f x'' h1). Qed.
Lemma lem3586752 {A B : Type'} (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : (term45 A B f x'' y) = y.
Proof. exact (@lem3586751 A B y x' f x'' h1). Qed.
Lemma lem3586753 {A B : Type'} (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : term152 A B f x'' y.
Proof. exact (fun h0 : term153 A B f x'' y => @lem3586752 A B y x' f x'' h1). Qed.
Lemma lem3586755 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3586756 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : (term152 A B f x'' y) = ((term45 A B f x'' y) = y).
Proof. exact (@lem3586755 ((term45 A B f x'' y) = y)). Qed.
Lemma lem3586757 {A B : Type'} (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term357 A B x' f x'') : (term45 A B f x'' y) = y.
Proof. exact (EQ_MP (@lem3586756 A B f x'' y) (@lem3586753 A B y x' f x'' h1)). Qed.
Lemma lem3586760 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3586762 {A B : Type'} (f : A -> B) (_38737 : A) (y : B) : (term237 A B f _38737 y) = (term435 A B f _38737 y).
Proof. exact (@lem3586760 ((f _38737) = y)). Qed.
Lemma lem3586765 {A B : Type'} (_38737 : A) (f : A -> B) (y : B) (h1 : term242 A B f y) : term435 A B f _38737 y.
Proof. exact (EQ_MP (@lem3586762 A B f _38737 y) (@lem3586677 A B _38737 f y h1)). Qed.
Lemma lem3586766 {A B : Type'} (_38737 : A) (f : A -> B) (y : B) (h1 : term242 A B f y) : term435 A B f _38737 y.
Proof. exact (@lem3586765 A B _38737 f y h1). Qed.
Lemma lem3586767 {A B : Type'} (x'' : B -> A) (f : A -> B) (y : B) (h1 : term242 A B f y) : term436 A B f x'' y.
Proof. exact (@lem3586766 A B (x'' y) f y h1). Qed.
Lemma lem3586770 {A B : Type'} (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term242 A B f y) (h2 : term357 A B x' f x'') : False.
Proof. exact (@lem3586767 A B x'' f y h1 (@lem3586757 A B y x' f x'' h2)). Qed.
Lemma lem3586771 {A B : Type'} (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term242 A B f y) (h2 : term357 A B x' f x'') : term144.
Proof. exact (fun h0 : ~ False => @lem3586770 A B y x' f x'' h1 h2). Qed.
Lemma lem3586773 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3586774 : term144 = False.
Proof. exact (@lem3586773 False). Qed.
Lemma lem3586775 {A B : Type'} (y : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term242 A B f y) (h2 : term357 A B x' f x'') : False.
Proof. exact (EQ_MP (@lem3586774) (@lem3586771 A B y x' f x'' h1 h2)). Qed.
Lemma lem3586776 {A B : Type'} (y : B) (x : A) (y' : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term242 A B f y) (h2 : term418 A B x y' x' f x'') : False.
Proof. exact (or_elim (@lem3586603 A B x y' x' f x'' h2) (fun h0 : term298 A B x f y' => @lem3586720 A B x f y' h0) (fun h0 : term357 A B x' f x'' => @lem3586775 A B y x' f x'' h1 h0)). Qed.
Lemma lem3586777 {A B : Type'} (y : B) (x : A) (y' : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term242 A B f y) (h2 : term418 A B x y' x' f x'') : (term418 A B x y' x' f x'') = False.
Proof. exact (prop_ext (fun h3 : term418 A B x y' x' f x'' => @lem3586776 A B y x y' x' f x'' h1 h2) (fun h3 : False => @lem3586603 A B x y' x' f x'' h2)). Qed.
Lemma lem3586778 {A B : Type'} (y : B) (x : A) (y' : B) (x' : A -> A) (f : A -> B) (x'' : B -> A) (h1 : term242 A B f y) (h2 : term418 A B x y' x' f x'') : False.
Proof. exact (EQ_MP (@lem3586777 A B y x y' x' f x'' h1 h2) (@lem3586603 A B x y' x' f x'' h2)). Qed.
Lemma lem3586779 {A B : Type'} (x : A) (y' : B) (x' : A -> A) (f : A -> B) (y : B) (h1 : term421 A B x y' x' f) (h2 : term242 A B f y) : False.
Proof. exact (ex_elim (@lem3586527 A B x y' x' f h1) (fun x'' : B -> A => fun h0 : term420 A B x y' x' f x'' => @lem3586778 A B y x y' x' f x'' h2 h0)). Qed.
Lemma lem3586780 {A B : Type'} (x : A) (y' : B) (f : A -> B) (y : B) (h1 : term423 A B x y' f) (h2 : term242 A B f y) : False.
Proof. exact (ex_elim (@lem3586526 A B x y' f h1) (fun x' : A -> A => fun h0 : term422 A B x y' f x' => @lem3586779 A B x y' x' f y h0 h2)). Qed.
Lemma lem3586781 {A B : Type'} (x : A) (f : A -> B) (y : B) (h1 : term425 A B x f) (h2 : term242 A B f y) : False.
Proof. exact (ex_elim (@lem3586525 A B x f h1) (fun y' : B => fun h0 : term424 A B x f y' => @lem3586780 A B x y' f y h0 h2)). Qed.
Lemma lem3586782 {A B : Type'} (y : B) (f : A -> B) (h1 : term242 A B f y) (h2 : (term225 A B f) = (term231 A B f)) : False.
Proof. exact (ex_elim (@lem3586504 A B f h2) (fun x : A => fun h0 : term426 A B f x => @lem3586781 A B x f y h0 h1)). Qed.
Lemma lem3586783 {A B : Type'} (y : B) (f : A -> B) (h1 : term242 A B f y) (h2 : (term225 A B f) = (term231 A B f)) : (term242 A B f y) = False.
Proof. exact (prop_ext (fun h3 : term242 A B f y => @lem3586782 A B y f h1 h2) (fun h3 : False => @lem3586129 A B f y h1)). Qed.
Lemma lem3586784 {A B : Type'} (y : B) (f : A -> B) (h1 : term242 A B f y) (h2 : (term225 A B f) = (term231 A B f)) : False.
Proof. exact (EQ_MP (@lem3586783 A B y f h1 h2) (@lem3586129 A B f y h1)). Qed.
Lemma lem3586785 {A B : Type'} (y : B) (f : A -> B) (h1 : (term225 A B f) = (term231 A B f)) : term241 A B f y.
Proof. exact (fun h0 : term242 A B f y => @lem3586784 A B y f h0 h1). Qed.
Lemma lem3586786 {A B : Type'} (y : B) (f : A -> B) (h1 : (term225 A B f) = (term231 A B f)) : term22 A B f y.
Proof. exact (EQ_MP (@lem3586128 A B f y) (@lem3586785 A B y f h1)). Qed.
Lemma lem3586791 {A B : Type'} (f : A -> B) (h1 : (term225 A B f) = (term231 A B f)) : term24 A B f.
Proof. exact (fun y : B => @lem3586786 A B y f h1). Qed.
Lemma lem3586792 {A B : Type'} (f : A -> B) : term234 A B f.
Proof. exact (fun h0 : (term225 A B f) = (term231 A B f) => @lem3586791 A B f h0). Qed.
Lemma lem3586797 {A B : Type'} : term236 A B.
Proof. exact (fun f : A -> B => @lem3586792 A B f). Qed.
Lemma lem3586798 {A B : Type'} : term219 A B.
Proof. exact (EQ_MP (@lem3586123 A B) (@lem3586797 A B)). Qed.
Lemma lem3586799 {A B : Type'} (f : A -> B) : term437 A B f.
Proof. exact (@lem3586798 A B f). Qed.
Lemma lem3586800 {A B : Type'} (f : A -> B) : (term437 A B f) = (term211 A B f).
Proof. exact (eq_refl (term437 A B f)). Qed.
Lemma lem3586801 {A B : Type'} (f : A -> B) : term211 A B f.
Proof. exact (EQ_MP (@lem3586800 A B f) (@lem3586799 A B f)). Qed.
Lemma lem3586803 {A B : Type'} (f : A -> B) : term211 A B f.
Proof. exact (@lem3585976 A B f (@lem3586801 A B f)). Qed.
Lemma lem3586804 {A B : Type'} (f : A -> B) (h1 : term212 A B f) : False.
Proof. exact (@lem3586803 A B f (@lem3585960 A B f h1)). Qed.
Lemma lem3586805 {A B : Type'} (f : A -> B) (h1 : term212 A B f) : (term212 A B f) = False.
Proof. exact (prop_ext (fun h2 : term212 A B f => @lem3586804 A B f h1) (fun h2 : False => @lem3585960 A B f h1)). Qed.
Lemma lem3586806 {A B : Type'} (f : A -> B) (h1 : term212 A B f) : False.
Proof. exact (EQ_MP (@lem3586805 A B f h1) (@lem3585960 A B f h1)). Qed.
Lemma lem3586807 {A B : Type'} (f : A -> B) : term211 A B f.
Proof. exact (fun h0 : term212 A B f => @lem3586806 A B f h0). Qed.
Lemma lem3586808 {A B : Type'} (f : A -> B) : term210 A B f.
Proof. exact (EQ_MP (@lem3585959 A B f) (@lem3586807 A B f)). Qed.
Lemma lem3586809 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : term24 A B f.
Proof. exact (@lem3586808 A B f (@lem3585955 A B f h1)). Qed.
Lemma lem3586810 {A B : Type'} (f : A -> B) : term438 A B f.
Proof. exact (fun h0 : term20 A B f => @lem3586809 A B f h0). Qed.
Lemma lem3586811 {A B : Type'} (f : A -> B) : term439 A B f.
Proof. exact (conj (@lem3585951 A B f) (@lem3586810 A B f)). Qed.
Lemma lem3586812 {A B : Type'} (f : A -> B) : (term439 A B f) = ((term24 A B f) = (term20 A B f)).
Proof. exact (@lem32 (term24 A B f) (term20 A B f)). Qed.
Lemma lem3586813 {A B : Type'} (f : A -> B) : (term24 A B f) = (term20 A B f).
Proof. exact (EQ_MP (@lem3586812 A B f) (@lem3586811 A B f)). Qed.
Lemma lem3586818 {A B : Type'} : term440 A B.
Proof. exact (fun f : A -> B => @lem3586813 A B f). Qed.
