Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_FORALL_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Lemma lem3584076 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3584077 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (@lem3584076 (term1 A B f)). Qed.
Lemma lem3584078 {A B : Type'} (f : A -> B) : (term2 A B f) = (term1 A B f).
Proof. exact (SYM (@lem3584077 A B f)). Qed.
Lemma lem3584079 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : term3 A B f.
Proof. exact (h1). Qed.
Lemma lem3584082 {A B : Type'} (f : A -> B) (h1 : term2 A B f) : term2 A B f.
Proof. exact (h1). Qed.
Lemma lem3584083 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (fun h0 : term2 A B f => @lem3584082 A B f h0). Qed.
Lemma lem3584084 {A B : Type'} (f : A -> B) (h1 : term4 A B f) : term4 A B f.
Proof. exact (h1). Qed.
Lemma lem3584085 {A B : Type'} (f : A -> B) (h1 : term2 A B f) : term2 A B f.
Proof. exact (h1). Qed.
Lemma lem3584086 {A B : Type'} (f : A -> B) (h1 : term2 A B f) (h2 : term4 A B f) : term2 A B f.
Proof. exact (@lem3584084 A B f h2 (@lem3584085 A B f h1)). Qed.
Lemma lem3584087 {A B : Type'} (f : A -> B) (h1 : term2 A B f) : term5 A B f.
Proof. exact (fun h0 : term4 A B f => @lem3584086 A B f h1 h0). Qed.
Lemma lem3584088 {A B : Type'} (f : A -> B) (h1 : term4 A B f) : term4 A B f.
Proof. exact (h1). Qed.
Lemma lem3584089 {A B : Type'} (f : A -> B) (h1 : term2 A B f) (h2 : term4 A B f) : term2 A B f.
Proof. exact (@lem3584087 A B f h1 (@lem3584088 A B f h2)). Qed.
Lemma lem3584090 {A B : Type'} (f : A -> B) (h1 : term4 A B f) : term4 A B f.
Proof. exact (fun h0 : term2 A B f => @lem3584089 A B f h0 h1). Qed.
Lemma lem3584091 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (fun h0 : term4 A B f => @lem3584090 A B f h0). Qed.
Lemma lem3584094 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem3584091 A B f (@lem3584083 A B f)). Qed.
Lemma lem3584095 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem3584094 A B f). Qed.
Lemma lem3584101 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3584102 {A B : Type'} (f : A -> B) : (term2 A B f) = (term7 A B f).
Proof. exact (@lem3584101 (term3 A B f)). Qed.
Lemma lem3584104 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3584105 {A B : Type'} (f : A -> B) : (term7 A B f) = (term1 A B f).
Proof. exact (@lem3584104 (term1 A B f)). Qed.
Lemma lem3584108 {A B : Type'} (f : A -> B) : (term2 A B f) = (term1 A B f).
Proof. exact (TRANS (@lem3584102 A B f) (@lem3584105 A B f)). Qed.
Lemma lem3584129 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3584108 A B f)). Qed.
Lemma lem3584130 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3584139 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem3584130 A B) (@lem3584129 A B)). Qed.
Lemma lem3584140 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3584141 {B : Type'} (P : B -> Prop) : (term13 B P) = (term13 B P).
Proof. exact (fun_ext (fun y : B => @lem3584140 B P y)). Qed.
Lemma lem3584142 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584143 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (MK_COMB (@lem3584142 B) (@lem3584141 B P)). Qed.
Lemma lem3584144 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term15 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term15 A B P f x)). Qed.
Lemma lem3584145 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term16 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3584144 A B P f x)). Qed.
Lemma lem3584146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584147 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term17 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3584146 A) (@lem3584145 A B P f)). Qed.
Lemma lem3584148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584149 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term18 A B P f) = (term18 A B P f).
Proof. exact (MK_COMB (@lem3584148) (@lem3584147 A B P f)). Qed.
Lemma lem3584150 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term17 A B P f) = (term14 B P)) = ((term17 A B P f) = (term14 B P)).
Proof. exact (MK_COMB (@lem3584149 A B P f) (@lem3584143 B P)). Qed.
Lemma lem3584151 {A B : Type'} (f : A -> B) : (term19 A B f) = (term19 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem3584150 A B f P)). Qed.
Lemma lem3584152 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3584153 {A B : Type'} (f : A -> B) : (term20 A B f) = (term20 A B f).
Proof. exact (MK_COMB (@lem3584152 B) (@lem3584151 A B f)). Qed.
Lemma lem3584154 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3584155 {A B : Type'} (f : A -> B) (y : B) : (term21 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3584154 A B f x y)). Qed.
Lemma lem3584156 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584157 {A B : Type'} (f : A -> B) (y : B) : (term22 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3584156 A) (@lem3584155 A B f y)). Qed.
Lemma lem3584158 {A B : Type'} (f : A -> B) : (term23 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3584157 A B f y)). Qed.
Lemma lem3584159 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584160 {A B : Type'} (f : A -> B) : (term24 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3584159 B) (@lem3584158 A B f)). Qed.
Lemma lem3584161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3584162 {A B : Type'} (f : A -> B) : (term25 A B f) = (term25 A B f).
Proof. exact (MK_COMB (@lem3584161) (@lem3584160 A B f)). Qed.
Lemma lem3584163 {A B : Type'} (f : A -> B) : (term1 A B f) = (term1 A B f).
Proof. exact (MK_COMB (@lem3584162 A B f) (@lem3584153 A B f)). Qed.
Lemma lem3584164 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3584163 A B f)). Qed.
Lemma lem3584165 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3584166 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem3584165 A B) (@lem3584164 A B)). Qed.
Lemma lem3584207 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (TRANS (@lem3584139 A B) (@lem3584166 A B)). Qed.
Lemma lem3584208 {A B : Type'} : (term12 A B) = (term11 A B).
Proof. exact (SYM (@lem3584207 A B)). Qed.
Lemma lem3584209 {A B : Type'} (f : A -> B) (h1 : term24 A B f) : term24 A B f.
Proof. exact (h1). Qed.
Lemma lem3584211 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3584212 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term17 A B P f) = (term14 B P)) = (term26 A B f P).
Proof. exact (@lem3584211 ((term17 A B P f) = (term14 B P))). Qed.
Lemma lem3584213 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term26 A B f P) = ((term17 A B P f) = (term14 B P)).
Proof. exact (SYM (@lem3584212 A B f P)). Qed.
Lemma lem3584214 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term27 A B f P) : term27 A B f P.
Proof. exact (h1). Qed.
Lemma lem3584215 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3584216 {A B : Type'} (f : A -> B) (y : B) : (term21 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3584215 A B f x y)). Qed.
Lemma lem3584217 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584218 {A B : Type'} (f : A -> B) (y : B) : (term22 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3584217 A) (@lem3584216 A B f y)). Qed.
Lemma lem3584219 {A B : Type'} (f : A -> B) : (term23 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3584218 A B f y)). Qed.
Lemma lem3584220 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584221 {A B : Type'} (f : A -> B) : (term24 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3584220 B) (@lem3584219 A B f)). Qed.
Lemma lem3584232 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3584233 {A B : Type'} (P : type1470 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (@lem3584232 B A P). Qed.
Lemma lem3584234 {A B : Type'} (f : A -> B) : (term32 A B f) = (term33 A B f).
Proof. exact (@lem3584233 A B (term34 A B f)). Qed.
Lemma lem3584235 {A B : Type'} (f : A -> B) (y : B) : (term35 A B f y) = (term21 A B f y).
Proof. exact (eq_refl (term35 A B f y)). Qed.
Lemma lem3584236 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3584237 {A B : Type'} (f : A -> B) (y : B) (x : A) : (term36 A B f y x) = (term37 A B f y x).
Proof. exact (MK_COMB (@lem3584235 A B f y) (@lem3584236 A x)). Qed.
Lemma lem3584238 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term37 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term37 A B f y x)). Qed.
Lemma lem3584239 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term36 A B f y x) = ((f x) = y).
Proof. exact (TRANS (@lem3584237 A B f y x) (@lem3584238 A B f x y)). Qed.
Lemma lem3584240 {A B : Type'} (f : A -> B) (y : B) : (term38 A B f y) = (term21 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3584239 A B f x y)). Qed.
Lemma lem3584241 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584242 {A B : Type'} (f : A -> B) (y : B) : (term39 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3584241 A) (@lem3584240 A B f y)). Qed.
Lemma lem3584243 {A B : Type'} (f : A -> B) : (term40 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3584242 A B f y)). Qed.
Lemma lem3584244 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584245 {A B : Type'} (f : A -> B) : (term32 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3584244 B) (@lem3584243 A B f)). Qed.
Lemma lem3584246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584247 {A B : Type'} (f : A -> B) : (term41 A B f) = (term42 A B f).
Proof. exact (MK_COMB (@lem3584246) (@lem3584245 A B f)). Qed.
Lemma lem3584248 {A B : Type'} (f : A -> B) (y : B) : (term35 A B f y) = (term21 A B f y).
Proof. exact (eq_refl (term35 A B f y)). Qed.
Lemma lem3584249 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3584250 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term43 A B f x y) = (term44 A B f x y).
Proof. exact (MK_COMB (@lem3584248 A B f y) (@lem3584249 A B x y)). Qed.
Lemma lem3584251 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term44 A B f x y) = ((term45 A B f x y) = y).
Proof. exact (eq_refl (term44 A B f x y)). Qed.
Lemma lem3584252 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term43 A B f x y) = ((term45 A B f x y) = y).
Proof. exact (TRANS (@lem3584250 A B f x y) (@lem3584251 A B f x y)). Qed.
Lemma lem3584253 {A B : Type'} (f : A -> B) (x : B -> A) : (term46 A B f x) = (term47 A B f x).
Proof. exact (fun_ext (fun y : B => @lem3584252 A B f x y)). Qed.
Lemma lem3584254 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584255 {A B : Type'} (f : A -> B) (x : B -> A) : (term48 A B f x) = (term49 A B f x).
Proof. exact (MK_COMB (@lem3584254 B) (@lem3584253 A B f x)). Qed.
Lemma lem3584256 {A B : Type'} (f : A -> B) : (term50 A B f) = (term51 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem3584255 A B f x)). Qed.
Lemma lem3584257 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3584258 {A B : Type'} (f : A -> B) : (term33 A B f) = (term52 A B f).
Proof. exact (MK_COMB (@lem3584257 A B) (@lem3584256 A B f)). Qed.
Lemma lem3584259 {A B : Type'} (f : A -> B) : ((term32 A B f) = (term33 A B f)) = ((term24 A B f) = (term52 A B f)).
Proof. exact (MK_COMB (@lem3584247 A B f) (@lem3584258 A B f)). Qed.
Lemma lem3584261 {A B : Type'} (f : A -> B) : (term24 A B f) = (term52 A B f).
Proof. exact (EQ_MP (@lem3584259 A B f) (@lem3584234 A B f)). Qed.
Lemma lem3584262 {A B : Type'} (f : A -> B) : (term24 A B f) = (term52 A B f).
Proof. exact (TRANS (@lem3584221 A B f) (@lem3584261 A B f)). Qed.
Lemma lem3584263 {A B : Type'} (f : A -> B) (h1 : term24 A B f) : term52 A B f.
Proof. exact (EQ_MP (@lem3584262 A B f) (@lem3584209 A B f h1)). Qed.
Lemma lem3584265 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term15 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term15 A B P f x)). Qed.
Lemma lem3584266 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3584267 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term55 A B P f) = (term56 A B P f).
Proof. exact (@lem3584266 A (term16 A B P f)). Qed.
Lemma lem3584268 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term57 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term57 A B P f x)). Qed.
Lemma lem3584269 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3584271 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term58 A B P f x) = (term59 A B P f x).
Proof. exact (MK_COMB (@lem3584269) (@lem3584268 A B P f x)). Qed.
Lemma lem3584272 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term60 A B P f) = (term61 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3584271 A B P f x)). Qed.
Lemma lem3584273 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584274 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term56 A B P f) = (term62 A B P f).
Proof. exact (MK_COMB (@lem3584273 A) (@lem3584272 A B P f)). Qed.
Lemma lem3584275 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term55 A B P f) = (term62 A B P f).
Proof. exact (TRANS (@lem3584267 A B P f) (@lem3584274 A B P f)). Qed.
Lemma lem3584276 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term16 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3584265 A B P f x)). Qed.
Lemma lem3584277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584278 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term17 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3584277 A) (@lem3584276 A B P f)). Qed.
Lemma lem3584280 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3584281 {B : Type'} (P : B -> Prop) : (term53 B P) = (term54 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3584282 {B : Type'} (P : B -> Prop) : (term63 B P) = (term64 B P).
Proof. exact (@lem3584281 B (term13 B P)). Qed.
Lemma lem3584283 {B : Type'} (P : B -> Prop) (y : B) : (term65 B P y) = (P y).
Proof. exact (eq_refl (term65 B P y)). Qed.
Lemma lem3584284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3584286 {B : Type'} (P : B -> Prop) (y : B) : (term66 B P y) = (term67 B P y).
Proof. exact (MK_COMB (@lem3584284) (@lem3584283 B P y)). Qed.
Lemma lem3584287 {B : Type'} (P : B -> Prop) : (term68 B P) = (term69 B P).
Proof. exact (fun_ext (fun y : B => @lem3584286 B P y)). Qed.
Lemma lem3584288 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3584289 {B : Type'} (P : B -> Prop) : (term64 B P) = (term54 B P).
Proof. exact (MK_COMB (@lem3584288 B) (@lem3584287 B P)). Qed.
Lemma lem3584290 {B : Type'} (P : B -> Prop) : (term63 B P) = (term54 B P).
Proof. exact (TRANS (@lem3584282 B P) (@lem3584289 B P)). Qed.
Lemma lem3584291 {B : Type'} (P : B -> Prop) : (term13 B P) = (term13 B P).
Proof. exact (fun_ext (fun y : B => @lem3584280 B P y)). Qed.
Lemma lem3584292 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584293 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (MK_COMB (@lem3584292 B) (@lem3584291 B P)). Qed.
Lemma lem3584294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3584295 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term70 A B P f) = (term71 A B P f).
Proof. exact (MK_COMB (@lem3584294) (@lem3584275 A B P f)). Qed.
Lemma lem3584296 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term72 A B f P) = (term73 A B f P).
Proof. exact (MK_COMB (@lem3584295 A B P f) (@lem3584293 B P)). Qed.
Lemma lem3584297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3584298 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term74 A B P f) = (term74 A B P f).
Proof. exact (MK_COMB (@lem3584297) (@lem3584278 A B P f)). Qed.
Lemma lem3584299 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term75 A B f P) = (term76 A B f P).
Proof. exact (MK_COMB (@lem3584298 A B P f) (@lem3584290 B P)). Qed.
Lemma lem3584300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3584301 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term77 A B f P) = (term78 A B f P).
Proof. exact (MK_COMB (@lem3584300) (@lem3584299 A B f P)). Qed.
Lemma lem3584302 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term79 A B f P) = (term80 A B f P).
Proof. exact (MK_COMB (@lem3584301 A B f P) (@lem3584296 A B f P)). Qed.
Lemma lem3584303 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term27 A B f P) = (term79 A B f P).
Proof. exact (@lem17646 (term17 A B P f) (term14 B P)). Qed.
Lemma lem3584304 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term27 A B f P) = (term80 A B f P).
Proof. exact (TRANS (@lem3584303 A B f P) (@lem3584302 A B f P)). Qed.
Lemma lem3584323 {A : Type'} (P : Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3584324 {B : Type'} (P : Prop) (Q : B -> Prop) : (term81 B P Q) = (term82 B P Q).
Proof. exact (@lem3584323 B P Q). Qed.
Lemma lem3584325 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term83 A B f P) = (term84 A B f P).
Proof. exact (@lem3584324 B (term17 A B P f) (term69 B P)). Qed.
Lemma lem3584326 {B : Type'} (P : B -> Prop) (y : B) : (term85 B P y) = (term67 B P y).
Proof. exact (eq_refl (term85 B P y)). Qed.
Lemma lem3584327 {B : Type'} (P : B -> Prop) : (term86 B P) = (term69 B P).
Proof. exact (fun_ext (fun y : B => @lem3584326 B P y)). Qed.
Lemma lem3584328 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3584329 {B : Type'} (P : B -> Prop) : (term87 B P) = (term54 B P).
Proof. exact (MK_COMB (@lem3584328 B) (@lem3584327 B P)). Qed.
Lemma lem3584330 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term74 A B P f) = (term74 A B P f).
Proof. exact (eq_refl (term74 A B P f)). Qed.
Lemma lem3584331 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term83 A B f P) = (term76 A B f P).
Proof. exact (MK_COMB (@lem3584330 A B P f) (@lem3584329 B P)). Qed.
Lemma lem3584332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584333 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term88 A B f P) = (term89 A B f P).
Proof. exact (MK_COMB (@lem3584332) (@lem3584331 A B f P)). Qed.
Lemma lem3584334 {B : Type'} (P : B -> Prop) (y : B) : (term85 B P y) = (term67 B P y).
Proof. exact (eq_refl (term85 B P y)). Qed.
Lemma lem3584335 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term74 A B P f) = (term74 A B P f).
Proof. exact (eq_refl (term74 A B P f)). Qed.
Lemma lem3584336 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term90 A B f P y) = (term91 A B f P y).
Proof. exact (MK_COMB (@lem3584335 A B P f) (@lem3584334 B P y)). Qed.
Lemma lem3584337 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term92 A B f P) = (term93 A B f P).
Proof. exact (fun_ext (fun y : B => @lem3584336 A B f P y)). Qed.
Lemma lem3584338 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3584339 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term84 A B f P) = (term94 A B f P).
Proof. exact (MK_COMB (@lem3584338 B) (@lem3584337 A B f P)). Qed.
Lemma lem3584340 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term83 A B f P) = (term84 A B f P)) = ((term76 A B f P) = (term94 A B f P)).
Proof. exact (MK_COMB (@lem3584333 A B f P) (@lem3584339 A B f P)). Qed.
Lemma lem3584341 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term76 A B f P) = (term94 A B f P).
Proof. exact (EQ_MP (@lem3584340 A B f P) (@lem3584325 A B f P)). Qed.
Lemma lem3584342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3584343 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term78 A B f P) = (term95 A B f P).
Proof. exact (MK_COMB (@lem3584342) (@lem3584341 A B f P)). Qed.
Lemma lem3584345 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3584346 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (@lem3584345 A P Q). Qed.
Lemma lem3584347 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term98 A B f P) = (term99 A B f P).
Proof. exact (@lem3584346 A (term61 A B P f) (term14 B P)). Qed.
Lemma lem3584348 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term100 A B P f x) = (term59 A B P f x).
Proof. exact (eq_refl (term100 A B P f x)). Qed.
Lemma lem3584349 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term101 A B P f) = (term61 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3584348 A B P f x)). Qed.
Lemma lem3584350 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584351 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term102 A B P f) = (term62 A B P f).
Proof. exact (MK_COMB (@lem3584350 A) (@lem3584349 A B P f)). Qed.
Lemma lem3584352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3584353 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term103 A B P f) = (term71 A B P f).
Proof. exact (MK_COMB (@lem3584352) (@lem3584351 A B P f)). Qed.
Lemma lem3584354 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (eq_refl (term14 B P)). Qed.
Lemma lem3584355 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term98 A B f P) = (term73 A B f P).
Proof. exact (MK_COMB (@lem3584353 A B P f) (@lem3584354 B P)). Qed.
Lemma lem3584356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584357 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term104 A B f P) = (term105 A B f P).
Proof. exact (MK_COMB (@lem3584356) (@lem3584355 A B f P)). Qed.
Lemma lem3584358 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term100 A B P f x) = (term59 A B P f x).
Proof. exact (eq_refl (term100 A B P f x)). Qed.
Lemma lem3584359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3584360 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term106 A B P f x) = (term107 A B P f x).
Proof. exact (MK_COMB (@lem3584359) (@lem3584358 A B P f x)). Qed.
Lemma lem3584361 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (eq_refl (term14 B P)). Qed.
Lemma lem3584362 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term108 A B f x P) = (term109 A B f x P).
Proof. exact (MK_COMB (@lem3584360 A B P f x) (@lem3584361 B P)). Qed.
Lemma lem3584363 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term110 A B f P) = (term111 A B f P).
Proof. exact (fun_ext (fun x : A => @lem3584362 A B f x P)). Qed.
Lemma lem3584364 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584365 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term99 A B f P) = (term112 A B f P).
Proof. exact (MK_COMB (@lem3584364 A) (@lem3584363 A B f P)). Qed.
Lemma lem3584366 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term98 A B f P) = (term99 A B f P)) = ((term73 A B f P) = (term112 A B f P)).
Proof. exact (MK_COMB (@lem3584357 A B f P) (@lem3584365 A B f P)). Qed.
Lemma lem3584367 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term73 A B f P) = (term112 A B f P).
Proof. exact (EQ_MP (@lem3584366 A B f P) (@lem3584347 A B f P)). Qed.
Lemma lem3584368 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term80 A B f P) = (term113 A B f P).
Proof. exact (MK_COMB (@lem3584343 A B f P) (@lem3584367 A B f P)). Qed.
Lemma lem3584372 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3584373 {B : Type'} (P : B -> Prop) (Q : Prop) : (term114 B P Q) = (term115 B P Q).
Proof. exact (@lem3584372 B P Q). Qed.
Lemma lem3584374 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term116 A B f P) = (term117 A B f P).
Proof. exact (@lem3584373 B (term93 A B f P) (term112 A B f P)). Qed.
Lemma lem3584375 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term118 A B f P y) = (term91 A B f P y).
Proof. exact (eq_refl (term118 A B f P y)). Qed.
Lemma lem3584376 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term119 A B f P) = (term93 A B f P).
Proof. exact (fun_ext (fun y : B => @lem3584375 A B f P y)). Qed.
Lemma lem3584377 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3584378 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term120 A B f P) = (term94 A B f P).
Proof. exact (MK_COMB (@lem3584377 B) (@lem3584376 A B f P)). Qed.
Lemma lem3584379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3584380 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term121 A B f P) = (term95 A B f P).
Proof. exact (MK_COMB (@lem3584379) (@lem3584378 A B f P)). Qed.
Lemma lem3584381 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term112 A B f P) = (term112 A B f P).
Proof. exact (eq_refl (term112 A B f P)). Qed.
Lemma lem3584382 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term116 A B f P) = (term113 A B f P).
Proof. exact (MK_COMB (@lem3584380 A B f P) (@lem3584381 A B f P)). Qed.
Lemma lem3584383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584384 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term122 A B f P) = (term123 A B f P).
Proof. exact (MK_COMB (@lem3584383) (@lem3584382 A B f P)). Qed.
Lemma lem3584385 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term118 A B f P y) = (term91 A B f P y).
Proof. exact (eq_refl (term118 A B f P y)). Qed.
Lemma lem3584386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3584387 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term124 A B f P y) = (term125 A B f P y).
Proof. exact (MK_COMB (@lem3584386) (@lem3584385 A B f P y)). Qed.
Lemma lem3584388 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term112 A B f P) = (term112 A B f P).
Proof. exact (eq_refl (term112 A B f P)). Qed.
Lemma lem3584389 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term126 A B y f P) = (term127 A B y f P).
Proof. exact (MK_COMB (@lem3584387 A B f P y) (@lem3584388 A B f P)). Qed.
Lemma lem3584390 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term128 A B f P) = (term129 A B f P).
Proof. exact (fun_ext (fun y : B => @lem3584389 A B y f P)). Qed.
Lemma lem3584391 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3584392 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term117 A B f P) = (term130 A B f P).
Proof. exact (MK_COMB (@lem3584391 B) (@lem3584390 A B f P)). Qed.
Lemma lem3584393 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term116 A B f P) = (term117 A B f P)) = ((term113 A B f P) = (term130 A B f P)).
Proof. exact (MK_COMB (@lem3584384 A B f P) (@lem3584392 A B f P)). Qed.
Lemma lem3584394 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term113 A B f P) = (term130 A B f P).
Proof. exact (EQ_MP (@lem3584393 A B f P) (@lem3584374 A B f P)). Qed.
Lemma lem3584396 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3584397 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (@lem3584396 A P Q). Qed.
Lemma lem3584398 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term133 A B y f P) = (term134 A B y f P).
Proof. exact (@lem3584397 A (term91 A B f P y) (term111 A B f P)). Qed.
Lemma lem3584399 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term135 A B f P x) = (term109 A B f x P).
Proof. exact (eq_refl (term135 A B f P x)). Qed.
Lemma lem3584400 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term136 A B f P) = (term111 A B f P).
Proof. exact (fun_ext (fun x : A => @lem3584399 A B f x P)). Qed.
Lemma lem3584401 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584402 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term137 A B f P) = (term112 A B f P).
Proof. exact (MK_COMB (@lem3584401 A) (@lem3584400 A B f P)). Qed.
Lemma lem3584403 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term125 A B f P y) = (term125 A B f P y).
Proof. exact (eq_refl (term125 A B f P y)). Qed.
Lemma lem3584404 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term133 A B y f P) = (term127 A B y f P).
Proof. exact (MK_COMB (@lem3584403 A B f P y) (@lem3584402 A B f P)). Qed.
Lemma lem3584405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584406 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term138 A B y f P) = (term139 A B y f P).
Proof. exact (MK_COMB (@lem3584405) (@lem3584404 A B y f P)). Qed.
Lemma lem3584407 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term135 A B f P x) = (term109 A B f x P).
Proof. exact (eq_refl (term135 A B f P x)). Qed.
Lemma lem3584408 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term125 A B f P y) = (term125 A B f P y).
Proof. exact (eq_refl (term125 A B f P y)). Qed.
Lemma lem3584409 {A B : Type'} (y : B) (f : A -> B) (x : A) (P : B -> Prop) : (term140 A B y f P x) = (term141 A B y f x P).
Proof. exact (MK_COMB (@lem3584408 A B f P y) (@lem3584407 A B f x P)). Qed.
Lemma lem3584410 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term142 A B y f P) = (term143 A B y f P).
Proof. exact (fun_ext (fun x : A => @lem3584409 A B y f x P)). Qed.
Lemma lem3584411 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584412 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term134 A B y f P) = (term144 A B y f P).
Proof. exact (MK_COMB (@lem3584411 A) (@lem3584410 A B y f P)). Qed.
Lemma lem3584413 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : ((term133 A B y f P) = (term134 A B y f P)) = ((term127 A B y f P) = (term144 A B y f P)).
Proof. exact (MK_COMB (@lem3584406 A B y f P) (@lem3584412 A B y f P)). Qed.
Lemma lem3584414 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) : (term127 A B y f P) = (term144 A B y f P).
Proof. exact (EQ_MP (@lem3584413 A B y f P) (@lem3584398 A B y f P)). Qed.
Lemma lem3584415 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term129 A B f P) = (term145 A B f P).
Proof. exact (fun_ext (fun y : B => @lem3584414 A B y f P)). Qed.
Lemma lem3584416 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3584417 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term130 A B f P) = (term146 A B f P).
Proof. exact (MK_COMB (@lem3584416 B) (@lem3584415 A B f P)). Qed.
Lemma lem3584418 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term113 A B f P) = (term146 A B f P).
Proof. exact (TRANS (@lem3584394 A B f P) (@lem3584417 A B f P)). Qed.
Lemma lem3584420 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term80 A B f P) = (term146 A B f P).
Proof. exact (TRANS (@lem3584368 A B f P) (@lem3584418 A B f P)). Qed.
Lemma lem3584421 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term27 A B f P) = (term146 A B f P).
Proof. exact (TRANS (@lem3584304 A B f P) (@lem3584420 A B f P)). Qed.
Lemma lem3584422 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term27 A B f P) : term146 A B f P.
Proof. exact (EQ_MP (@lem3584421 A B f P) (@lem3584214 A B f P h1)). Qed.
Lemma lem3584423 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) (h1 : term144 A B y f P) : term144 A B y f P.
Proof. exact (h1). Qed.
Lemma lem3584424 {A B : Type'} (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term141 A B y f x P) : term141 A B y f x P.
Proof. exact (h1). Qed.
Lemma lem3584425 {A B : Type'} (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term49 A B f x'.
Proof. exact (h1). Qed.
Lemma lem3584428 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3584429 {B : Type'} (P : B -> Prop) : (term13 B P) = (term13 B P).
Proof. exact (fun_ext (fun y : B => @lem3584428 B P y)). Qed.
Lemma lem3584430 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584431 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (MK_COMB (@lem3584430 B) (@lem3584429 B P)). Qed.
Lemma lem3584440 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term107 A B P f x) = (term107 A B P f x).
Proof. exact (eq_refl (term107 A B P f x)). Qed.
Lemma lem3584441 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) : (term109 A B f x P) = (term109 A B f x P).
Proof. exact (MK_COMB (@lem3584440 A B P f x) (@lem3584431 B P)). Qed.
Lemma lem3584446 {B : Type'} (P : B -> Prop) (y : B) : (term67 B P y) = (term67 B P y).
Proof. exact (eq_refl (term67 B P y)). Qed.
Lemma lem3584451 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term15 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term15 A B P f x)). Qed.
Lemma lem3584452 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term16 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3584451 A B P f x)). Qed.
Lemma lem3584453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584454 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term17 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3584453 A) (@lem3584452 A B P f)). Qed.
Lemma lem3584455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3584456 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term74 A B P f) = (term74 A B P f).
Proof. exact (MK_COMB (@lem3584455) (@lem3584454 A B P f)). Qed.
Lemma lem3584457 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term91 A B f P y) = (term91 A B f P y).
Proof. exact (MK_COMB (@lem3584456 A B P f) (@lem3584446 B P y)). Qed.
Lemma lem3584458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3584459 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) : (term125 A B f P y) = (term125 A B f P y).
Proof. exact (MK_COMB (@lem3584458) (@lem3584457 A B f P y)). Qed.
Lemma lem3584460 {A B : Type'} (y : B) (f : A -> B) (x : A) (P : B -> Prop) : (term141 A B y f x P) = (term141 A B y f x P).
Proof. exact (MK_COMB (@lem3584459 A B f P y) (@lem3584441 A B f x P)). Qed.
Lemma lem3584461 {A B : Type'} (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term141 A B y f x P) : term141 A B y f x P.
Proof. exact (EQ_MP (@lem3584460 A B y f x P) (@lem3584424 A B y f x P h1)). Qed.
Lemma lem3584470 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : ((term45 A B f x' y) = y) = ((term45 A B f x' y) = y).
Proof. exact (eq_refl ((term45 A B f x' y) = y)). Qed.
Lemma lem3584471 {A B : Type'} (f : A -> B) (x' : B -> A) : (term47 A B f x') = (term47 A B f x').
Proof. exact (fun_ext (fun y : B => @lem3584470 A B f x' y)). Qed.
Lemma lem3584472 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584473 {A B : Type'} (f : A -> B) (x' : B -> A) : (term49 A B f x') = (term49 A B f x').
Proof. exact (MK_COMB (@lem3584472 B) (@lem3584471 A B f x')). Qed.
Lemma lem3584474 {A B : Type'} (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term49 A B f x'.
Proof. exact (EQ_MP (@lem3584473 A B f x') (@lem3584425 A B f x' h1)). Qed.
Lemma lem3584475 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term91 A B f P y.
Proof. exact (h1). Qed.
Lemma lem3584476 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term109 A B f x P.
Proof. exact (h1). Qed.
Lemma lem3584478 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term17 A B P f.
Proof. exact (proj1 (@lem3584475 A B f P y h1)). Qed.
Lemma lem3584479 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term14 B P.
Proof. exact (proj2 (@lem3584476 A B f x P h1)). Qed.
Lemma lem3584482 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : ((term45 A B f x' y) = y) = ((term45 A B f x' y) = y).
Proof. exact (eq_refl ((term45 A B f x' y) = y)). Qed.
Lemma lem3584483 {A B : Type'} (f : A -> B) (x' : B -> A) : (term47 A B f x') = (term47 A B f x').
Proof. exact (fun_ext (fun y : B => @lem3584482 A B f x' y)). Qed.
Lemma lem3584484 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584486 {A B : Type'} (f : A -> B) (x' : B -> A) : (term49 A B f x') = (term49 A B f x').
Proof. exact (MK_COMB (@lem3584484 B) (@lem3584483 A B f x')). Qed.
Lemma lem3584487 {A B : Type'} (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term49 A B f x'.
Proof. exact (EQ_MP (@lem3584486 A B f x') (@lem3584474 A B f x' h1)). Qed.
Lemma lem3584489 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term15 A B P f x) = (term15 A B P f x).
Proof. exact (eq_refl (term15 A B P f x)). Qed.
Lemma lem3584490 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term16 A B P f) = (term16 A B P f).
Proof. exact (fun_ext (fun x : A => @lem3584489 A B P f x)). Qed.
Lemma lem3584491 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584493 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term17 A B P f) = (term17 A B P f).
Proof. exact (MK_COMB (@lem3584491 A) (@lem3584490 A B P f)). Qed.
Lemma lem3584494 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term17 A B P f.
Proof. exact (EQ_MP (@lem3584493 A B P f) (@lem3584478 A B f P y h1)). Qed.
Lemma lem3584511 {B : Type'} (P : B -> Prop) (y : B) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3584512 {B : Type'} (P : B -> Prop) : (term13 B P) = (term13 B P).
Proof. exact (fun_ext (fun y : B => @lem3584511 B P y)). Qed.
Lemma lem3584513 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584515 {B : Type'} (P : B -> Prop) : (term14 B P) = (term14 B P).
Proof. exact (MK_COMB (@lem3584513 B) (@lem3584512 B P)). Qed.
Lemma lem3584516 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term14 B P.
Proof. exact (EQ_MP (@lem3584515 B P) (@lem3584479 A B f x P h1)). Qed.
Lemma lem3584517 {A B : Type'} (_38699 : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term147 A B f x' _38699.
Proof. exact (@lem3584487 A B f x' h1 _38699). Qed.
Lemma lem3584518 {A B : Type'} (f : A -> B) (x' : B -> A) (_38699 : B) : (term147 A B f x' _38699) = ((term45 A B f x' _38699) = _38699).
Proof. exact (eq_refl (term147 A B f x' _38699)). Qed.
Lemma lem3584520 {A B : Type'} (_38700 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term57 A B P f _38700.
Proof. exact (@lem3584494 A B f P y h1 _38700). Qed.
Lemma lem3584521 {A B : Type'} (P : B -> Prop) (f : A -> B) (_38700 : A) : (term57 A B P f _38700) = (term15 A B P f _38700).
Proof. exact (eq_refl (term57 A B P f _38700)). Qed.
Lemma lem3584526 {A B : Type'} (_38702 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term65 B P _38702.
Proof. exact (@lem3584516 A B f x P h1 _38702). Qed.
Lemma lem3584527 {B : Type'} (P : B -> Prop) (_38702 : B) : (term65 B P _38702) = (P _38702).
Proof. exact (eq_refl (term65 B P _38702)). Qed.
Lemma lem3584534 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term67 B P y.
Proof. exact (proj2 (@lem3584475 A B f P y h1)). Qed.
Lemma lem3584538 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term59 A B P f x.
Proof. exact (proj1 (@lem3584476 A B f x P h1)). Qed.
Lemma lem3584541 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3584542 {B : Type'} (_38703 : B) (_38704 : B) (h1 : _38703 = _38704) : _38703 = _38704.
Proof. exact (h1). Qed.
Lemma lem3584543 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) (h1 : _38703 = _38704) : (P _38703) = (P _38704).
Proof. exact (MK_COMB (@lem3584541 B P) (@lem3584542 B _38703 _38704 h1)). Qed.
Lemma lem3584545 (b : Prop) (a : Prop) : term148 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3584546 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : term149 B _38704 P _38703.
Proof. exact (@lem3584545 (P _38704) (P _38703)). Qed.
Lemma lem3584547 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) (h1 : _38703 = _38704) : term150 B _38704 P _38703.
Proof. exact (@lem3584546 B _38704 P _38703 (@lem3584543 B P _38703 _38704 h1)). Qed.
Lemma lem3584548 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : term151 B _38704 P _38703.
Proof. exact (fun h0 : _38703 = _38704 => @lem3584547 B P _38703 _38704 h0). Qed.
Lemma lem3584550 (a : Prop) (b : Prop) : (a -> b) = (term152 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3584551 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term151 B _38704 P _38703) = (term153 B _38704 P _38703).
Proof. exact (@lem3584550 (_38703 = _38704) (term150 B _38704 P _38703)). Qed.
Lemma lem3584552 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : term153 B _38704 P _38703.
Proof. exact (EQ_MP (@lem3584551 B _38704 P _38703) (@lem3584548 B _38704 P _38703)). Qed.
Lemma lem3584574 {A B : Type'} (_38699 : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' _38699) = _38699.
Proof. exact (EQ_MP (@lem3584518 A B f x' _38699) (@lem3584517 A B _38699 f x' h1)). Qed.
Lemma lem3584575 {A B : Type'} (_38699 : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' _38699) = _38699.
Proof. exact (@lem3584574 A B _38699 f x' h1). Qed.
Lemma lem3584576 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' y) = y.
Proof. exact (@lem3584575 A B y f x' h1). Qed.
Lemma lem3584577 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : term154 A B f x' y.
Proof. exact (fun h0 : term155 A B f x' y => @lem3584576 A B y f x' h1). Qed.
Lemma lem3584579 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584580 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term154 A B f x' y) = ((term45 A B f x' y) = y).
Proof. exact (@lem3584579 ((term45 A B f x' y) = y)). Qed.
Lemma lem3584581 {A B : Type'} (y : B) (f : A -> B) (x' : B -> A) (h1 : term49 A B f x') : (term45 A B f x' y) = y.
Proof. exact (EQ_MP (@lem3584580 A B f x' y) (@lem3584577 A B y f x' h1)). Qed.
Lemma lem3584583 {A B : Type'} (_38700 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term15 A B P f _38700.
Proof. exact (EQ_MP (@lem3584521 A B P f _38700) (@lem3584520 A B _38700 f P y h1)). Qed.
Lemma lem3584584 {A B : Type'} (_38700 : A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term15 A B P f _38700.
Proof. exact (@lem3584583 A B _38700 f P y h1). Qed.
Lemma lem3584585 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term157 A B P f x' y.
Proof. exact (@lem3584584 A B (x' y) f P y h1). Qed.
Lemma lem3584586 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term158 A B P f x' y.
Proof. exact (fun h0 : term159 A B P f x' y => @lem3584585 A B x' f P y h1). Qed.
Lemma lem3584588 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584589 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term158 A B P f x' y) = (term157 A B P f x' y).
Proof. exact (@lem3584588 (term157 A B P f x' y)). Qed.
Lemma lem3584590 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term157 A B P f x' y.
Proof. exact (EQ_MP (@lem3584589 A B P f x' y) (@lem3584586 A B x' f P y h1)). Qed.
Lemma lem3584596 (q : Prop) (p : Prop) (r : Prop) : (term160 p q r) = (term160 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3584597 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term153 B _38704 P _38703) = (term161 B _38704 P _38703).
Proof. exact (@lem3584596 (P _38704) (term162 B _38703 _38704) (term67 B P _38703)). Qed.
Lemma lem3584611 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3584612 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : (term163 B _38704 P _38703) = (term164 B P _38703 _38704).
Proof. exact (@lem3584611 (term67 B P _38703) (term162 B _38703 _38704)). Qed.
Lemma lem3584620 {B : Type'} (P : B -> Prop) (_38704 : B) : (term165 B P _38704) = (term165 B P _38704).
Proof. exact (eq_refl (term165 B P _38704)). Qed.
Lemma lem3584621 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : (term161 B _38704 P _38703) = (term166 B P _38703 _38704).
Proof. exact (MK_COMB (@lem3584620 B P _38704) (@lem3584612 B P _38703 _38704)). Qed.
Lemma lem3584632 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : (term153 B _38704 P _38703) = (term166 B P _38703 _38704).
Proof. exact (TRANS (@lem3584597 B _38704 P _38703) (@lem3584621 B P _38703 _38704)). Qed.
Lemma lem3584633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584634 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : (term167 B _38704 P _38703) = (term168 B P _38703 _38704).
Proof. exact (MK_COMB (@lem3584633) (@lem3584632 B P _38703 _38704)). Qed.
Lemma lem3584648 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3584649 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : (term163 B _38704 P _38703) = (term164 B P _38703 _38704).
Proof. exact (@lem3584648 (term67 B P _38703) (term162 B _38703 _38704)). Qed.
Lemma lem3584657 {B : Type'} (P : B -> Prop) (_38704 : B) : (term165 B P _38704) = (term165 B P _38704).
Proof. exact (eq_refl (term165 B P _38704)). Qed.
Lemma lem3584658 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : (term161 B _38704 P _38703) = (term166 B P _38703 _38704).
Proof. exact (MK_COMB (@lem3584657 B P _38704) (@lem3584649 B P _38703 _38704)). Qed.
Lemma lem3584669 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : ((term153 B _38704 P _38703) = (term161 B _38704 P _38703)) = ((term166 B P _38703 _38704) = (term166 B P _38703 _38704)).
Proof. exact (MK_COMB (@lem3584634 B P _38703 _38704) (@lem3584658 B P _38703 _38704)). Qed.
Lemma lem3584671 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3584672 (x : Prop) : (x = x) = True.
Proof. exact (@lem3584671 Prop x). Qed.
Lemma lem3584673 {B : Type'} (P : B -> Prop) (_38703 : B) (_38704 : B) : ((term166 B P _38703 _38704) = (term166 B P _38703 _38704)) = True.
Proof. exact (@lem3584672 (term166 B P _38703 _38704)). Qed.
Lemma lem3584674 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : ((term153 B _38704 P _38703) = (term161 B _38704 P _38703)) = True.
Proof. exact (TRANS (@lem3584669 B P _38703 _38704) (@lem3584673 B P _38703 _38704)). Qed.
Lemma lem3584675 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : True = ((term153 B _38704 P _38703) = (term161 B _38704 P _38703)).
Proof. exact (SYM (@lem3584674 B _38704 P _38703)). Qed.
Lemma lem3584676 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term153 B _38704 P _38703) = (term161 B _38704 P _38703).
Proof. exact (EQ_MP (@lem3584675 B _38704 P _38703) (@lem0)). Qed.
Lemma lem3584677 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : term161 B _38704 P _38703.
Proof. exact (EQ_MP (@lem3584676 B _38704 P _38703) (@lem3584552 B _38704 P _38703)). Qed.
Lemma lem3584679 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3584680 {B : Type'} (_38703 : B) (P : B -> Prop) (_38704 : B) : (term161 B _38704 P _38703) = (term170 B _38703 P _38704).
Proof. exact (@lem3584679 (term163 B _38704 P _38703) (P _38704)). Qed.
Lemma lem3584682 (a : Prop) (b : Prop) : (term171 a b) = (term172 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3584683 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term173 B _38704 P _38703) = (term174 B _38704 P _38703).
Proof. exact (@lem3584682 (term162 B _38703 _38704) (term67 B P _38703)). Qed.
Lemma lem3584685 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3584686 {B : Type'} (_38703 : B) (_38704 : B) : (term175 B _38703 _38704) = (_38703 = _38704).
Proof. exact (@lem3584685 (_38703 = _38704)). Qed.
Lemma lem3584687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3584688 {B : Type'} (_38703 : B) (_38704 : B) : (term176 B _38703 _38704) = (term177 B _38703 _38704).
Proof. exact (MK_COMB (@lem3584687) (@lem3584686 B _38703 _38704)). Qed.
Lemma lem3584690 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3584691 {B : Type'} (P : B -> Prop) (_38703 : B) : (term178 B P _38703) = (P _38703).
Proof. exact (@lem3584690 (P _38703)). Qed.
Lemma lem3584692 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term174 B _38704 P _38703) = (term179 B _38704 P _38703).
Proof. exact (MK_COMB (@lem3584688 B _38703 _38704) (@lem3584691 B P _38703)). Qed.
Lemma lem3584693 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term173 B _38704 P _38703) = (term179 B _38704 P _38703).
Proof. exact (TRANS (@lem3584683 B _38704 P _38703) (@lem3584692 B _38704 P _38703)). Qed.
Lemma lem3584694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3584695 {B : Type'} (_38704 : B) (P : B -> Prop) (_38703 : B) : (term180 B _38704 P _38703) = (term181 B _38704 P _38703).
Proof. exact (MK_COMB (@lem3584694) (@lem3584693 B _38704 P _38703)). Qed.
Lemma lem3584696 {B : Type'} (P : B -> Prop) (_38704 : B) : (P _38704) = (P _38704).
Proof. exact (eq_refl (P _38704)). Qed.
Lemma lem3584697 {B : Type'} (_38703 : B) (P : B -> Prop) (_38704 : B) : (term170 B _38703 P _38704) = (term182 B _38703 P _38704).
Proof. exact (MK_COMB (@lem3584695 B _38704 P _38703) (@lem3584696 B P _38704)). Qed.
Lemma lem3584698 {B : Type'} (_38703 : B) (P : B -> Prop) (_38704 : B) : (term161 B _38704 P _38703) = (term182 B _38703 P _38704).
Proof. exact (TRANS (@lem3584680 B _38703 P _38704) (@lem3584697 B _38703 P _38704)). Qed.
Lemma lem3584700 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : term183 A B P f x' y.
Proof. exact (conj (@lem3584581 A B y f x' h1) (@lem3584590 A B x' f P y h2)). Qed.
Lemma lem3584702 {B : Type'} (_38703 : B) (P : B -> Prop) (_38704 : B) : term182 B _38703 P _38704.
Proof. exact (EQ_MP (@lem3584698 B _38703 P _38704) (@lem3584677 B _38704 P _38703)). Qed.
Lemma lem3584703 {B : Type'} (_38703 : B) (P : B -> Prop) (_38704 : B) : term182 B _38703 P _38704.
Proof. exact (@lem3584702 B _38703 P _38704). Qed.
Lemma lem3584704 {A B : Type'} (f : A -> B) (x' : B -> A) (P : B -> Prop) (y : B) : term184 A B f x' P y.
Proof. exact (@lem3584703 B (term45 A B f x' y) P y). Qed.
Lemma lem3584707 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : P y.
Proof. exact (@lem3584704 A B f x' P y (@lem3584700 A B x' f P y h1 h2)). Qed.
Lemma lem3584708 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : term185 B P y.
Proof. exact (fun h0 : term67 B P y => @lem3584707 A B x' f P y h1 h2). Qed.
Lemma lem3584710 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584711 {B : Type'} (P : B -> Prop) (y : B) : (term185 B P y) = (P y).
Proof. exact (@lem3584710 (P y)). Qed.
Lemma lem3584712 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : P y.
Proof. exact (EQ_MP (@lem3584711 B P y) (@lem3584708 A B x' f P y h1 h2)). Qed.
Lemma lem3584715 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3584717 {B : Type'} (P : B -> Prop) (y : B) : (term67 B P y) = (term186 B P y).
Proof. exact (@lem3584715 (P y)). Qed.
Lemma lem3584720 {A B : Type'} (f : A -> B) (P : B -> Prop) (y : B) (h1 : term91 A B f P y) : term186 B P y.
Proof. exact (EQ_MP (@lem3584717 B P y) (@lem3584534 A B f P y h1)). Qed.
Lemma lem3584723 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : False.
Proof. exact (@lem3584720 A B f P y h2 (@lem3584712 A B x' f P y h1 h2)). Qed.
Lemma lem3584724 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : term187.
Proof. exact (fun h0 : ~ False => @lem3584723 A B x' f P y h1 h2). Qed.
Lemma lem3584726 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584727 : term187 = False.
Proof. exact (@lem3584726 False). Qed.
Lemma lem3584728 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : False.
Proof. exact (EQ_MP (@lem3584727) (@lem3584724 A B x' f P y h1 h2)). Qed.
Lemma lem3584762 {A B : Type'} (_38702 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : P _38702.
Proof. exact (EQ_MP (@lem3584527 B P _38702) (@lem3584526 A B _38702 f x P h1)). Qed.
Lemma lem3584763 {A B : Type'} (_38702 : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : P _38702.
Proof. exact (@lem3584762 A B _38702 f x P h1). Qed.
Lemma lem3584764 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term15 A B P f x.
Proof. exact (@lem3584763 A B (f x) f x P h1). Qed.
Lemma lem3584765 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term188 A B P f x.
Proof. exact (fun h0 : term59 A B P f x => @lem3584764 A B f x P h1). Qed.
Lemma lem3584767 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584768 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term188 A B P f x) = (term15 A B P f x).
Proof. exact (@lem3584767 (term15 A B P f x)). Qed.
Lemma lem3584769 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term15 A B P f x.
Proof. exact (EQ_MP (@lem3584768 A B P f x) (@lem3584765 A B f x P h1)). Qed.
Lemma lem3584772 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3584774 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term59 A B P f x) = (term189 A B P f x).
Proof. exact (@lem3584772 (term15 A B P f x)). Qed.
Lemma lem3584777 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term189 A B P f x.
Proof. exact (EQ_MP (@lem3584774 A B P f x) (@lem3584538 A B f x P h1)). Qed.
Lemma lem3584780 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : False.
Proof. exact (@lem3584777 A B f x P h1 (@lem3584769 A B f x P h1)). Qed.
Lemma lem3584781 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : term187.
Proof. exact (fun h0 : ~ False => @lem3584780 A B f x P h1). Qed.
Lemma lem3584783 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3584784 : term187 = False.
Proof. exact (@lem3584783 False). Qed.
Lemma lem3584785 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (h1 : term109 A B f x P) : False.
Proof. exact (EQ_MP (@lem3584784) (@lem3584781 A B f x P h1)). Qed.
Lemma lem3584786 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : (term49 A B f x') = False.
Proof. exact (prop_ext (fun h3 : term49 A B f x' => @lem3584728 A B x' f P y h1 h2) (fun h3 : False => @lem3584487 A B f x' h1)). Qed.
Lemma lem3584787 {A B : Type'} (x' : B -> A) (f : A -> B) (P : B -> Prop) (y : B) (h1 : term49 A B f x') (h2 : term91 A B f P y) : False.
Proof. exact (EQ_MP (@lem3584786 A B x' f P y h1 h2) (@lem3584487 A B f x' h1)). Qed.
Lemma lem3584788 {A B : Type'} (x' : B -> A) (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term49 A B f x') (h2 : term141 A B y f x P) : False.
Proof. exact (or_elim (@lem3584461 A B y f x P h2) (fun h0 : term91 A B f P y => @lem3584787 A B x' f P y h1 h0) (fun h0 : term109 A B f x P => @lem3584785 A B f x P h0)). Qed.
Lemma lem3584789 {A B : Type'} (x' : B -> A) (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term49 A B f x') (h2 : term141 A B y f x P) : (term49 A B f x') = False.
Proof. exact (prop_ext (fun h3 : term49 A B f x' => @lem3584788 A B x' y f x P h1 h2) (fun h3 : False => @lem3584474 A B f x' h1)). Qed.
Lemma lem3584790 {A B : Type'} (x' : B -> A) (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term49 A B f x') (h2 : term141 A B y f x P) : False.
Proof. exact (EQ_MP (@lem3584789 A B x' y f x P h1 h2) (@lem3584474 A B f x' h1)). Qed.
Lemma lem3584791 {A B : Type'} (x' : B -> A) (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term49 A B f x') (h2 : term141 A B y f x P) : (term141 A B y f x P) = False.
Proof. exact (prop_ext (fun h3 : term141 A B y f x P => @lem3584790 A B x' y f x P h1 h2) (fun h3 : False => @lem3584461 A B y f x P h2)). Qed.
Lemma lem3584792 {A B : Type'} (x' : B -> A) (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term49 A B f x') (h2 : term141 A B y f x P) : False.
Proof. exact (EQ_MP (@lem3584791 A B x' y f x P h1 h2) (@lem3584461 A B y f x P h2)). Qed.
Lemma lem3584793 {A B : Type'} (y : B) (f : A -> B) (x : A) (P : B -> Prop) (h1 : term24 A B f) (h2 : term141 A B y f x P) : False.
Proof. exact (ex_elim (@lem3584263 A B f h1) (fun x' : B -> A => fun h0 : term51 A B f x' => @lem3584792 A B x' y f x P h0 h2)). Qed.
Lemma lem3584794 {A B : Type'} (y : B) (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term144 A B y f P) : False.
Proof. exact (ex_elim (@lem3584423 A B y f P h2) (fun x : A => fun h0 : term143 A B y f P x => @lem3584793 A B y f x P h1 h0)). Qed.
Lemma lem3584795 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term27 A B f P) : False.
Proof. exact (ex_elim (@lem3584422 A B f P h2) (fun y : B => fun h0 : term145 A B f P y => @lem3584794 A B y f P h1 h0)). Qed.
Lemma lem3584796 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term27 A B f P) : (term27 A B f P) = False.
Proof. exact (prop_ext (fun h3 : term27 A B f P => @lem3584795 A B f P h1 h2) (fun h3 : False => @lem3584214 A B f P h2)). Qed.
Lemma lem3584797 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : term24 A B f) (h2 : term27 A B f P) : False.
Proof. exact (EQ_MP (@lem3584796 A B f P h1 h2) (@lem3584214 A B f P h2)). Qed.
Lemma lem3584798 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term24 A B f) : term26 A B f P.
Proof. exact (fun h0 : term27 A B f P => @lem3584797 A B f P h1 h0). Qed.
Lemma lem3584799 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term24 A B f) : (term17 A B P f) = (term14 B P).
Proof. exact (EQ_MP (@lem3584213 A B f P) (@lem3584798 A B P f h1)). Qed.
Lemma lem3584804 {A B : Type'} (f : A -> B) (h1 : term24 A B f) : term20 A B f.
Proof. exact (fun P : B -> Prop => @lem3584799 A B P f h1). Qed.
Lemma lem3584805 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (fun h0 : term24 A B f => @lem3584804 A B f h0). Qed.
Lemma lem3584810 {A B : Type'} : term12 A B.
Proof. exact (fun f : A -> B => @lem3584805 A B f). Qed.
Lemma lem3584811 {A B : Type'} : term11 A B.
Proof. exact (EQ_MP (@lem3584208 A B) (@lem3584810 A B)). Qed.
Lemma lem3584812 {A B : Type'} (f : A -> B) : term190 A B f.
Proof. exact (@lem3584811 A B f). Qed.
Lemma lem3584813 {A B : Type'} (f : A -> B) : (term190 A B f) = (term2 A B f).
Proof. exact (eq_refl (term190 A B f)). Qed.
Lemma lem3584814 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem3584813 A B f) (@lem3584812 A B f)). Qed.
Lemma lem3584816 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (@lem3584095 A B f (@lem3584814 A B f)). Qed.
Lemma lem3584817 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : False.
Proof. exact (@lem3584816 A B f (@lem3584079 A B f h1)). Qed.
Lemma lem3584818 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : (term3 A B f) = False.
Proof. exact (prop_ext (fun h2 : term3 A B f => @lem3584817 A B f h1) (fun h2 : False => @lem3584079 A B f h1)). Qed.
Lemma lem3584819 {A B : Type'} (f : A -> B) (h1 : term3 A B f) : False.
Proof. exact (EQ_MP (@lem3584818 A B f h1) (@lem3584079 A B f h1)). Qed.
Lemma lem3584820 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (fun h0 : term3 A B f => @lem3584819 A B f h0). Qed.
Lemma lem3584821 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem3584078 A B f) (@lem3584820 A B f)). Qed.
Lemma lem3584822 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : term20 A B f.
Proof. exact (h1). Qed.
Lemma lem3584824 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : (term17 A B P f) = (term14 B P)) : (term17 A B P f) = (term14 B P).
Proof. exact (h1). Qed.
Lemma lem3584825 {A B : Type'} (f : A -> B) (P : B -> Prop) (h1 : (term17 A B P f) = (term14 B P)) : (term14 B P) = (term17 A B P f).
Proof. exact (SYM (@lem3584824 A B f P h1)). Qed.
Lemma lem3584826 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : (term14 B P) = (term17 A B P f)) : (term14 B P) = (term17 A B P f).
Proof. exact (h1). Qed.
Lemma lem3584827 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : (term14 B P) = (term17 A B P f)) : (term17 A B P f) = (term14 B P).
Proof. exact (SYM (@lem3584826 A B P f h1)). Qed.
Lemma lem3584828 {A B : Type'} (P : B -> Prop) (f : A -> B) : ((term17 A B P f) = (term14 B P)) = ((term14 B P) = (term17 A B P f)).
Proof. exact (prop_ext (fun h1 : (term17 A B P f) = (term14 B P) => @lem3584825 A B f P h1) (fun h1 : (term14 B P) = (term17 A B P f) => @lem3584827 A B P f h1)). Qed.
Lemma lem3584829 {A B : Type'} (f : A -> B) : (term19 A B f) = (term191 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem3584828 A B P f)). Qed.
Lemma lem3584830 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3584831 {A B : Type'} (f : A -> B) : (term20 A B f) = (term192 A B f).
Proof. exact (MK_COMB (@lem3584830 B) (@lem3584829 A B f)). Qed.
Lemma lem3584832 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : term192 A B f.
Proof. exact (EQ_MP (@lem3584831 A B f) (@lem3584822 A B f h1)). Qed.
Lemma lem3584833 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term20 A B f) : term193 A B f P.
Proof. exact (@lem3584832 A B f h1 P). Qed.
Lemma lem3584834 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term193 A B f P) = ((term14 B P) = (term17 A B P f)).
Proof. exact (eq_refl (term193 A B f P)). Qed.
Lemma lem3584841 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term20 A B f) : (term14 B P) = (term17 A B P f).
Proof. exact (EQ_MP (@lem3584834 A B P f) (@lem3584833 A B P f h1)). Qed.
Lemma lem3584842 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term20 A B f) : (term14 B P) = (term17 A B P f).
Proof. exact (@lem3584841 A B P f h1). Qed.
Lemma lem3584843 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : (term194 A B f) = (term195 A B f).
Proof. exact (@lem3584842 A B (term23 A B f) f h1). Qed.
Lemma lem3584844 {A B : Type'} (f : A -> B) (y : B) : (term196 A B f y) = (term22 A B f y).
Proof. exact (eq_refl (term196 A B f y)). Qed.
Lemma lem3584845 {A B : Type'} (f : A -> B) : (term197 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun y : B => @lem3584844 A B f y)). Qed.
Lemma lem3584846 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3584847 {A B : Type'} (f : A -> B) : (term194 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3584846 B) (@lem3584845 A B f)). Qed.
Lemma lem3584848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3584849 {A B : Type'} (f : A -> B) : (term198 A B f) = (term42 A B f).
Proof. exact (MK_COMB (@lem3584848) (@lem3584847 A B f)). Qed.
Lemma lem3584850 {A B : Type'} (f : A -> B) (x : A) : (term199 A B f x) = (term200 A B f x).
Proof. exact (eq_refl (term199 A B f x)). Qed.
Lemma lem3584851 {A B : Type'} (f : A -> B) : (term201 A B f) = (term202 A B f).
Proof. exact (fun_ext (fun x : A => @lem3584850 A B f x)). Qed.
Lemma lem3584852 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584853 {A B : Type'} (f : A -> B) : (term195 A B f) = (term203 A B f).
Proof. exact (MK_COMB (@lem3584852 A) (@lem3584851 A B f)). Qed.
Lemma lem3584854 {A B : Type'} (f : A -> B) : ((term194 A B f) = (term195 A B f)) = ((term24 A B f) = (term203 A B f)).
Proof. exact (MK_COMB (@lem3584849 A B f) (@lem3584853 A B f)). Qed.
Lemma lem3584855 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : (term24 A B f) = (term203 A B f).
Proof. exact (EQ_MP (@lem3584854 A B f) (@lem3584843 A B f h1)). Qed.
Lemma lem3584856 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : (term203 A B f) = (term24 A B f).
Proof. exact (SYM (@lem3584855 A B f h1)). Qed.
Lemma lem3584858 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3584859 {A B : Type'} (f : A -> B) : (term203 A B f) = (term204 A B f).
Proof. exact (@lem3584858 (term203 A B f)). Qed.
Lemma lem3584860 {A B : Type'} (f : A -> B) : (term204 A B f) = (term203 A B f).
Proof. exact (SYM (@lem3584859 A B f)). Qed.
Lemma lem3584861 {A B : Type'} (f : A -> B) (h1 : term205 A B f) : term205 A B f.
Proof. exact (h1). Qed.
Lemma lem3584864 {A B : Type'} (f : A -> B) (h1 : term204 A B f) : term204 A B f.
Proof. exact (h1). Qed.
Lemma lem3584865 {A B : Type'} (f : A -> B) : term206 A B f.
Proof. exact (fun h0 : term204 A B f => @lem3584864 A B f h0). Qed.
Lemma lem3584866 {A B : Type'} (f : A -> B) (h1 : term206 A B f) : term206 A B f.
Proof. exact (h1). Qed.
Lemma lem3584867 {A B : Type'} (f : A -> B) (h1 : term204 A B f) : term204 A B f.
Proof. exact (h1). Qed.
Lemma lem3584868 {A B : Type'} (f : A -> B) (h1 : term204 A B f) (h2 : term206 A B f) : term204 A B f.
Proof. exact (@lem3584866 A B f h2 (@lem3584867 A B f h1)). Qed.
Lemma lem3584869 {A B : Type'} (f : A -> B) (h1 : term204 A B f) : term207 A B f.
Proof. exact (fun h0 : term206 A B f => @lem3584868 A B f h1 h0). Qed.
Lemma lem3584870 {A B : Type'} (f : A -> B) (h1 : term206 A B f) : term206 A B f.
Proof. exact (h1). Qed.
Lemma lem3584871 {A B : Type'} (f : A -> B) (h1 : term204 A B f) (h2 : term206 A B f) : term204 A B f.
Proof. exact (@lem3584869 A B f h1 (@lem3584870 A B f h2)). Qed.
Lemma lem3584872 {A B : Type'} (f : A -> B) (h1 : term206 A B f) : term206 A B f.
Proof. exact (fun h0 : term204 A B f => @lem3584871 A B f h0 h1). Qed.
Lemma lem3584873 {A B : Type'} (f : A -> B) : term208 A B f.
Proof. exact (fun h0 : term206 A B f => @lem3584872 A B f h0). Qed.
Lemma lem3584876 {A B : Type'} (f : A -> B) : term206 A B f.
Proof. exact (@lem3584873 A B f (@lem3584865 A B f)). Qed.
Lemma lem3584877 {A B : Type'} (f : A -> B) : term206 A B f.
Proof. exact (@lem3584876 A B f). Qed.
Lemma lem3584883 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3584884 {A B : Type'} (f : A -> B) : (term204 A B f) = (term209 A B f).
Proof. exact (@lem3584883 (term205 A B f)). Qed.
Lemma lem3584886 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3584887 {A B : Type'} (f : A -> B) : (term209 A B f) = (term203 A B f).
Proof. exact (@lem3584886 (term203 A B f)). Qed.
Lemma lem3584892 {A B : Type'} (f : A -> B) : (term204 A B f) = (term203 A B f).
Proof. exact (TRANS (@lem3584884 A B f) (@lem3584887 A B f)). Qed.
Lemma lem3584897 {A B : Type'} : (term210 A B) = (term211 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3584892 A B f)). Qed.
Lemma lem3584898 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3584907 {A B : Type'} : (term212 A B) = (term213 A B).
Proof. exact (MK_COMB (@lem3584898 A B) (@lem3584897 A B)). Qed.
Lemma lem3584908 {A B : Type'} (x' : A) (f : A -> B) (x : A) : ((f x') = (f x)) = ((f x') = (f x)).
Proof. exact (eq_refl ((f x') = (f x))). Qed.
Lemma lem3584909 {A B : Type'} (f : A -> B) (x : A) : (term214 A B f x) = (term214 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3584908 A B x' f x)). Qed.
Lemma lem3584910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3584911 {A B : Type'} (f : A -> B) (x : A) : (term200 A B f x) = (term200 A B f x).
Proof. exact (MK_COMB (@lem3584910 A) (@lem3584909 A B f x)). Qed.
Lemma lem3584912 {A B : Type'} (f : A -> B) : (term202 A B f) = (term202 A B f).
Proof. exact (fun_ext (fun x : A => @lem3584911 A B f x)). Qed.
Lemma lem3584913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584914 {A B : Type'} (f : A -> B) : (term203 A B f) = (term203 A B f).
Proof. exact (MK_COMB (@lem3584913 A) (@lem3584912 A B f)). Qed.
Lemma lem3584915 {A B : Type'} : (term211 A B) = (term211 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3584914 A B f)). Qed.
Lemma lem3584916 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3584917 {A B : Type'} : (term213 A B) = (term213 A B).
Proof. exact (MK_COMB (@lem3584916 A B) (@lem3584915 A B)). Qed.
Lemma lem3584938 {A B : Type'} : (term212 A B) = (term213 A B).
Proof. exact (TRANS (@lem3584907 A B) (@lem3584917 A B)). Qed.
Lemma lem3584939 {A B : Type'} : (term213 A B) = (term212 A B).
Proof. exact (SYM (@lem3584938 A B)). Qed.
Lemma lem3584941 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3584942 {A B : Type'} (f : A -> B) (x : A) : (term200 A B f x) = (term215 A B f x).
Proof. exact (@lem3584941 (term200 A B f x)). Qed.
Lemma lem3584943 {A B : Type'} (f : A -> B) (x : A) : (term215 A B f x) = (term200 A B f x).
Proof. exact (SYM (@lem3584942 A B f x)). Qed.
Lemma lem3584944 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : term216 A B f x.
Proof. exact (h1). Qed.
Lemma lem3584946 {A : Type'} (P : A -> Prop) : (term217 A P) = (term218 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3584947 {A B : Type'} (f : A -> B) (x : A) : (term216 A B f x) = (term219 A B f x).
Proof. exact (@lem3584946 A (term214 A B f x)). Qed.
Lemma lem3584948 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term220 A B f x x') = ((f x') = (f x)).
Proof. exact (eq_refl (term220 A B f x x')). Qed.
Lemma lem3584949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3584951 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term221 A B f x x') = (term222 A B x' f x).
Proof. exact (MK_COMB (@lem3584949) (@lem3584948 A B x' f x)). Qed.
Lemma lem3584952 {A B : Type'} (f : A -> B) (x : A) : (term223 A B f x) = (term224 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3584951 A B x' f x)). Qed.
Lemma lem3584953 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584954 {A B : Type'} (f : A -> B) (x : A) : (term219 A B f x) = (term225 A B f x).
Proof. exact (MK_COMB (@lem3584953 A) (@lem3584952 A B f x)). Qed.
Lemma lem3584963 {A B : Type'} (f : A -> B) (x : A) : (term216 A B f x) = (term225 A B f x).
Proof. exact (TRANS (@lem3584947 A B f x) (@lem3584954 A B f x)). Qed.
Lemma lem3584964 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : term225 A B f x.
Proof. exact (EQ_MP (@lem3584963 A B f x) (@lem3584944 A B f x h1)). Qed.
Lemma lem3584975 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term222 A B x' f x) = (term222 A B x' f x).
Proof. exact (eq_refl (term222 A B x' f x)). Qed.
Lemma lem3584976 {A B : Type'} (f : A -> B) (x : A) : (term224 A B f x) = (term224 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3584975 A B x' f x)). Qed.
Lemma lem3584977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584978 {A B : Type'} (f : A -> B) (x : A) : (term225 A B f x) = (term225 A B f x).
Proof. exact (MK_COMB (@lem3584977 A) (@lem3584976 A B f x)). Qed.
Lemma lem3584979 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : term225 A B f x.
Proof. exact (EQ_MP (@lem3584978 A B f x) (@lem3584964 A B f x h1)). Qed.
Lemma lem3584981 {A B : Type'} (x' : A) (f : A -> B) (x : A) : (term222 A B x' f x) = (term222 A B x' f x).
Proof. exact (eq_refl (term222 A B x' f x)). Qed.
Lemma lem3584982 {A B : Type'} (f : A -> B) (x : A) : (term224 A B f x) = (term224 A B f x).
Proof. exact (fun_ext (fun x' : A => @lem3584981 A B x' f x)). Qed.
Lemma lem3584983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3584985 {A B : Type'} (f : A -> B) (x : A) : (term225 A B f x) = (term225 A B f x).
Proof. exact (MK_COMB (@lem3584983 A) (@lem3584982 A B f x)). Qed.
Lemma lem3584986 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : term225 A B f x.
Proof. exact (EQ_MP (@lem3584985 A B f x) (@lem3584979 A B f x h1)). Qed.
Lemma lem3584987 {A B : Type'} (_38715 : A) (f : A -> B) (x : A) (h1 : term216 A B f x) : term226 A B f x _38715.
Proof. exact (@lem3584986 A B f x h1 _38715). Qed.
Lemma lem3584988 {A B : Type'} (_38715 : A) (f : A -> B) (x : A) : (term226 A B f x _38715) = (term222 A B _38715 f x).
Proof. exact (eq_refl (term226 A B f x _38715)). Qed.
Lemma lem3584991 {A B : Type'} (_38715 : A) (f : A -> B) (x : A) (h1 : term216 A B f x) : term222 A B _38715 f x.
Proof. exact (EQ_MP (@lem3584988 A B _38715 f x) (@lem3584987 A B _38715 f x h1)). Qed.
Lemma lem3585005 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3585006 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3585005 B x). Qed.
Lemma lem3585007 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3585006 B (f x)). Qed.
Lemma lem3585008 {A B : Type'} (f : A -> B) (x : A) : term227 A B f x.
Proof. exact (fun h0 : term228 A B f x => @lem3585007 A B f x). Qed.
Lemma lem3585010 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585011 {A B : Type'} (f : A -> B) (x : A) : (term227 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3585010 ((f x) = (f x))). Qed.
Lemma lem3585012 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3585011 A B f x) (@lem3585008 A B f x)). Qed.
Lemma lem3585015 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3585017 {A B : Type'} (_38715 : A) (f : A -> B) (x : A) : (term222 A B _38715 f x) = (term229 A B _38715 f x).
Proof. exact (@lem3585015 ((f _38715) = (f x))). Qed.
Lemma lem3585020 {A B : Type'} (_38715 : A) (f : A -> B) (x : A) (h1 : term216 A B f x) : term229 A B _38715 f x.
Proof. exact (EQ_MP (@lem3585017 A B _38715 f x) (@lem3584991 A B _38715 f x h1)). Qed.
Lemma lem3585021 {A B : Type'} (_38715 : A) (f : A -> B) (x : A) (h1 : term216 A B f x) : term229 A B _38715 f x.
Proof. exact (@lem3585020 A B _38715 f x h1). Qed.
Lemma lem3585022 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : term230 A B f x.
Proof. exact (@lem3585021 A B x f x h1). Qed.
Lemma lem3585025 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : False.
Proof. exact (@lem3585022 A B f x h1 (@lem3585012 A B f x)). Qed.
Lemma lem3585026 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : term187.
Proof. exact (fun h0 : ~ False => @lem3585025 A B f x h1). Qed.
Lemma lem3585028 (p : Prop) : (term156 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3585029 : term187 = False.
Proof. exact (@lem3585028 False). Qed.
Lemma lem3585030 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : False.
Proof. exact (EQ_MP (@lem3585029) (@lem3585026 A B f x h1)). Qed.
Lemma lem3585031 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : (term216 A B f x) = False.
Proof. exact (prop_ext (fun h2 : term216 A B f x => @lem3585030 A B f x h1) (fun h2 : False => @lem3584944 A B f x h1)). Qed.
Lemma lem3585032 {A B : Type'} (f : A -> B) (x : A) (h1 : term216 A B f x) : False.
Proof. exact (EQ_MP (@lem3585031 A B f x h1) (@lem3584944 A B f x h1)). Qed.
Lemma lem3585033 {A B : Type'} (f : A -> B) (x : A) : term215 A B f x.
Proof. exact (fun h0 : term216 A B f x => @lem3585032 A B f x h0). Qed.
Lemma lem3585034 {A B : Type'} (f : A -> B) (x : A) : term200 A B f x.
Proof. exact (EQ_MP (@lem3584943 A B f x) (@lem3585033 A B f x)). Qed.
Lemma lem3585039 {A B : Type'} (f : A -> B) : term203 A B f.
Proof. exact (fun x : A => @lem3585034 A B f x). Qed.
Lemma lem3585044 {A B : Type'} : term213 A B.
Proof. exact (fun f : A -> B => @lem3585039 A B f). Qed.
Lemma lem3585045 {A B : Type'} : term212 A B.
Proof. exact (EQ_MP (@lem3584939 A B) (@lem3585044 A B)). Qed.
Lemma lem3585046 {A B : Type'} (f : A -> B) : term231 A B f.
Proof. exact (@lem3585045 A B f). Qed.
Lemma lem3585047 {A B : Type'} (f : A -> B) : (term231 A B f) = (term204 A B f).
Proof. exact (eq_refl (term231 A B f)). Qed.
Lemma lem3585048 {A B : Type'} (f : A -> B) : term204 A B f.
Proof. exact (EQ_MP (@lem3585047 A B f) (@lem3585046 A B f)). Qed.
Lemma lem3585050 {A B : Type'} (f : A -> B) : term204 A B f.
Proof. exact (@lem3584877 A B f (@lem3585048 A B f)). Qed.
Lemma lem3585051 {A B : Type'} (f : A -> B) (h1 : term205 A B f) : False.
Proof. exact (@lem3585050 A B f (@lem3584861 A B f h1)). Qed.
Lemma lem3585052 {A B : Type'} (f : A -> B) (h1 : term205 A B f) : (term205 A B f) = False.
Proof. exact (prop_ext (fun h2 : term205 A B f => @lem3585051 A B f h1) (fun h2 : False => @lem3584861 A B f h1)). Qed.
Lemma lem3585053 {A B : Type'} (f : A -> B) (h1 : term205 A B f) : False.
Proof. exact (EQ_MP (@lem3585052 A B f h1) (@lem3584861 A B f h1)). Qed.
Lemma lem3585054 {A B : Type'} (f : A -> B) : term204 A B f.
Proof. exact (fun h0 : term205 A B f => @lem3585053 A B f h0). Qed.
Lemma lem3585055 {A B : Type'} (f : A -> B) : term203 A B f.
Proof. exact (EQ_MP (@lem3584860 A B f) (@lem3585054 A B f)). Qed.
Lemma lem3585056 {A B : Type'} (f : A -> B) (h1 : term20 A B f) : term24 A B f.
Proof. exact (EQ_MP (@lem3584856 A B f h1) (@lem3585055 A B f)). Qed.
Lemma lem3585057 {A B : Type'} (f : A -> B) : term232 A B f.
Proof. exact (fun h0 : term20 A B f => @lem3585056 A B f h0). Qed.
Lemma lem3585058 {A B : Type'} (f : A -> B) : term233 A B f.
Proof. exact (conj (@lem3584821 A B f) (@lem3585057 A B f)). Qed.
Lemma lem3585059 {A B : Type'} (f : A -> B) : (term233 A B f) = ((term24 A B f) = (term20 A B f)).
Proof. exact (@lem32 (term24 A B f) (term20 A B f)). Qed.
Lemma lem3585060 {A B : Type'} (f : A -> B) : (term24 A B f) = (term20 A B f).
Proof. exact (EQ_MP (@lem3585059 A B f) (@lem3585058 A B f)). Qed.
Lemma lem3585065 {A B : Type'} : term234 A B.
Proof. exact (fun f : A -> B => @lem3585060 A B f). Qed.
