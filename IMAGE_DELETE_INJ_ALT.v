Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_DELETE_INJ_ALT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3382024 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3382025 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3382026 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3382025 t1) (@lem3382024 t1)). Qed.
Lemma lem3382027 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3382026 t1 t2). Qed.
Lemma lem3382028 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3382029 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3382028 t1 t2) (@lem3382027 t1 t2)). Qed.
Lemma lem3382030 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3382029 t1 t2 t3). Qed.
Lemma lem3382031 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3382032 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3382031 t1 t2 t3) (@lem3382030 t1 t2 t3)). Qed.
Lemma lem3382033 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3382032 t1 t2 t3)). Qed.
Lemma lem3382075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3382076 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term7 B s t).
Proof. exact (@lem3382075 B s t). Qed.
Lemma lem3382077 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : ((term8 A B f s a) = (term9 A B s f a)) = (term10 A B s f a).
Proof. exact (@lem3382076 B (term8 A B f s a) (term9 A B s f a)). Qed.
Lemma lem3382086 {A B : Type'} (f : A -> B) (a : A) (s : A -> Prop) : (term11 A B f a s) = (term11 A B f a s).
Proof. exact (eq_refl (term11 A B f a s)). Qed.
Lemma lem3382087 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term12 A B s f a) = (term13 A B s f a).
Proof. exact (MK_COMB (@lem3382086 A B f a s) (@lem3382077 A B s f a)). Qed.
Lemma lem3382090 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term15 A B s f).
Proof. exact (fun_ext (fun a : A => @lem3382087 A B s f a)). Qed.
Lemma lem3382091 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382092 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term16 A B s f) = (term17 A B s f).
Proof. exact (MK_COMB (@lem3382091 A) (@lem3382090 A B s f)). Qed.
Lemma lem3382097 {A B : Type'} (f : A -> B) : (term18 A B f) = (term19 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3382092 A B s f)). Qed.
Lemma lem3382098 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3382099 {A B : Type'} (f : A -> B) : (term20 A B f) = (term21 A B f).
Proof. exact (MK_COMB (@lem3382098 A) (@lem3382097 A B f)). Qed.
Lemma lem3382104 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3382099 A B f)). Qed.
Lemma lem3382105 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3382106 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem3382105 A B) (@lem3382104 A B)). Qed.
Lemma lem3382111 {A B : Type'} : (term25 A B) = (term24 A B).
Proof. exact (SYM (@lem3382106 A B)). Qed.
Lemma lem3382141 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3382142 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3382141 A P x). Qed.
Lemma lem3382143 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3382142 A s x). Qed.
Lemma lem3382144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382145 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3382144) (@lem3382143 A s x)). Qed.
Lemma lem3382149 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3382150 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3382149 A P x). Qed.
Lemma lem3382151 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem3382150 A s y). Qed.
Lemma lem3382152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382153 {A : Type'} (s : A -> Prop) (y : A) : (term26 A y s) = (term27 A s y).
Proof. exact (MK_COMB (@lem3382152) (@lem3382151 A s y)). Qed.
Lemma lem3382156 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3382157 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term28 A B s x f y) = (term29 A B s x f y).
Proof. exact (MK_COMB (@lem3382153 A s y) (@lem3382156 A B x f y)). Qed.
Lemma lem3382160 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term30 A B s x f y) = (term31 A B s x f y).
Proof. exact (MK_COMB (@lem3382145 A s x) (@lem3382157 A B s x f y)). Qed.
Lemma lem3382163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3382164 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term32 A B s x f y) = (term33 A B s x f y).
Proof. exact (MK_COMB (@lem3382163) (@lem3382160 A B s x f y)). Qed.
Lemma lem3382167 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3382168 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term34 A B s f x y) = (term35 A B s f x y).
Proof. exact (MK_COMB (@lem3382164 A B s x f y) (@lem3382167 A x y)). Qed.
Lemma lem3382171 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term36 A B s f x) = (term37 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3382168 A B s f x y)). Qed.
Lemma lem3382172 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382173 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term38 A B s f x) = (term39 A B s f x).
Proof. exact (MK_COMB (@lem3382172 A) (@lem3382171 A B s f x)). Qed.
Lemma lem3382178 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term40 A B s f) = (term41 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3382173 A B s f x)). Qed.
Lemma lem3382179 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382180 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term42 A B s f) = (term43 A B s f).
Proof. exact (MK_COMB (@lem3382179 A) (@lem3382178 A B s f)). Qed.
Lemma lem3382185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382186 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term45 A B s f).
Proof. exact (MK_COMB (@lem3382185) (@lem3382180 A B s f)). Qed.
Lemma lem3382188 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3382189 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3382188 A P x). Qed.
Lemma lem3382190 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem3382189 A s a). Qed.
Lemma lem3382191 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) : (term46 A B f a s) = (term47 A B f s a).
Proof. exact (MK_COMB (@lem3382186 A B s f) (@lem3382190 A s a)). Qed.
Lemma lem3382194 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3382195 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) : (term11 A B f a s) = (term48 A B f s a).
Proof. exact (MK_COMB (@lem3382194) (@lem3382191 A B f s a)). Qed.
Lemma lem3382203 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term49 A B y f s) = (term50 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3382204 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term49 A B y f s) = (term50 A B y f s).
Proof. exact (@lem3382203 A B y f s). Qed.
Lemma lem3382205 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term51 A B x f s a) = (term52 A B x f s a).
Proof. exact (@lem3382204 A B x f (@DELETE A s a)). Qed.
Lemma lem3382215 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term53 A x s y) = (term54 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3382216 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term53 A x s y) = (term54 A s x y).
Proof. exact (@lem3382215 A s x y). Qed.
Lemma lem3382217 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term53 A x s a) = (term54 A s x a).
Proof. exact (@lem3382216 A s x a). Qed.
Lemma lem3382221 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3382222 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3382221 A P x). Qed.
Lemma lem3382223 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3382222 A s x). Qed.
Lemma lem3382224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382225 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3382224) (@lem3382223 A s x)). Qed.
Lemma lem3382228 {A : Type'} (x : A) (a : A) : (term55 A x a) = (term55 A x a).
Proof. exact (eq_refl (term55 A x a)). Qed.
Lemma lem3382229 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term54 A s x a) = (term56 A s x a).
Proof. exact (MK_COMB (@lem3382225 A s x) (@lem3382228 A x a)). Qed.
Lemma lem3382232 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term53 A x s a) = (term56 A s x a).
Proof. exact (TRANS (@lem3382217 A s x a) (@lem3382229 A s x a)). Qed.
Lemma lem3382233 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term57 A B x f x') = (term57 A B x f x').
Proof. exact (eq_refl (term57 A B x f x')). Qed.
Lemma lem3382234 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term58 A B x f x' s a) = (term59 A B x f s x' a).
Proof. exact (MK_COMB (@lem3382233 A B x f x') (@lem3382232 A s x' a)). Qed.
Lemma lem3382237 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term60 A B x f s a) = (term61 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3382234 A B x f s x' a)). Qed.
Lemma lem3382238 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382239 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term52 A B x f s a) = (term62 A B x f s a).
Proof. exact (MK_COMB (@lem3382238 A) (@lem3382237 A B x f s a)). Qed.
Lemma lem3382244 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term51 A B x f s a) = (term62 A B x f s a).
Proof. exact (TRANS (@lem3382205 A B x f s a) (@lem3382239 A B x f s a)). Qed.
Lemma lem3382245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3382246 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term63 A B x f s a) = (term64 A B x f s a).
Proof. exact (MK_COMB (@lem3382245) (@lem3382244 A B x f s a)). Qed.
Lemma lem3382248 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term53 A x s y) = (term54 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3382249 {B : Type'} (s : B -> Prop) (x : B) (y : B) : (term53 B x s y) = (term54 B s x y).
Proof. exact (@lem3382248 B s x y). Qed.
Lemma lem3382250 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term65 A B x s f a) = (term66 A B s x f a).
Proof. exact (@lem3382249 B (@IMAGE A B f s) x (f a)). Qed.
Lemma lem3382254 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term49 A B y f s) = (term50 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3382255 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term49 A B y f s) = (term50 A B y f s).
Proof. exact (@lem3382254 A B y f s). Qed.
Lemma lem3382256 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term49 A B x f s) = (term50 A B x f s).
Proof. exact (@lem3382255 A B x f s). Qed.
Lemma lem3382266 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3382267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3382266 A P x). Qed.
Lemma lem3382268 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3382267 A s x). Qed.
Lemma lem3382269 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term57 A B x f x') = (term57 A B x f x').
Proof. exact (eq_refl (term57 A B x f x')). Qed.
Lemma lem3382270 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term67 A B x f x' s) = (term68 A B x f s x').
Proof. exact (MK_COMB (@lem3382269 A B x f x') (@lem3382268 A s x')). Qed.
Lemma lem3382273 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term69 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3382270 A B x f s x')). Qed.
Lemma lem3382274 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382275 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term50 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3382274 A) (@lem3382273 A B x f s)). Qed.
Lemma lem3382280 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term49 A B x f s) = (term71 A B x f s).
Proof. exact (TRANS (@lem3382256 A B x f s) (@lem3382275 A B x f s)). Qed.
Lemma lem3382281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382282 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term72 A B x f s) = (term73 A B x f s).
Proof. exact (MK_COMB (@lem3382281) (@lem3382280 A B x f s)). Qed.
Lemma lem3382285 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term74 A B x f a) = (term74 A B x f a).
Proof. exact (eq_refl (term74 A B x f a)). Qed.
Lemma lem3382286 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term66 A B s x f a) = (term75 A B s x f a).
Proof. exact (MK_COMB (@lem3382282 A B x f s) (@lem3382285 A B x f a)). Qed.
Lemma lem3382289 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term65 A B x s f a) = (term75 A B s x f a).
Proof. exact (TRANS (@lem3382250 A B s x f a) (@lem3382286 A B s x f a)). Qed.
Lemma lem3382290 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term51 A B x f s a) = (term65 A B x s f a)) = ((term62 A B x f s a) = (term75 A B s x f a)).
Proof. exact (MK_COMB (@lem3382246 A B x f s a) (@lem3382289 A B s x f a)). Qed.
Lemma lem3382293 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term76 A B s f a) = (term77 A B s f a).
Proof. exact (fun_ext (fun x : B => @lem3382290 A B s x f a)). Qed.
Lemma lem3382294 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3382295 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term10 A B s f a) = (term78 A B s f a).
Proof. exact (MK_COMB (@lem3382294 B) (@lem3382293 A B s f a)). Qed.
Lemma lem3382300 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term13 A B s f a) = (term79 A B s f a).
Proof. exact (MK_COMB (@lem3382195 A B f s a) (@lem3382295 A B s f a)). Qed.
Lemma lem3382303 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term15 A B s f) = (term80 A B s f).
Proof. exact (fun_ext (fun a : A => @lem3382300 A B s f a)). Qed.
Lemma lem3382304 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382305 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term17 A B s f) = (term81 A B s f).
Proof. exact (MK_COMB (@lem3382304 A) (@lem3382303 A B s f)). Qed.
Lemma lem3382310 {A B : Type'} (f : A -> B) : (term19 A B f) = (term82 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3382305 A B s f)). Qed.
Lemma lem3382311 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3382312 {A B : Type'} (f : A -> B) : (term21 A B f) = (term83 A B f).
Proof. exact (MK_COMB (@lem3382311 A) (@lem3382310 A B f)). Qed.
Lemma lem3382317 {A B : Type'} : (term23 A B) = (term84 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3382312 A B f)). Qed.
Lemma lem3382318 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3382319 {A B : Type'} : (term25 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem3382318 A B) (@lem3382317 A B)). Qed.
Lemma lem3382324 {A B : Type'} : (term85 A B) = (term25 A B).
Proof. exact (SYM (@lem3382319 A B)). Qed.
Lemma lem3382326 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3382327 {A B : Type'} : (term85 A B) = (term87 A B).
Proof. exact (@lem3382326 (term85 A B)). Qed.
Lemma lem3382328 {A B : Type'} : (term87 A B) = (term85 A B).
Proof. exact (SYM (@lem3382327 A B)). Qed.
Lemma lem3382329 {A B : Type'} (h1 : term88 A B) : term88 A B.
Proof. exact (h1). Qed.
Lemma lem3382332 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (h1). Qed.
Lemma lem3382333 {A B : Type'} : term89 A B.
Proof. exact (fun h0 : term87 A B => @lem3382332 A B h0). Qed.
Lemma lem3382334 {A B : Type'} (h1 : term89 A B) : term89 A B.
Proof. exact (h1). Qed.
Lemma lem3382335 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (h1). Qed.
Lemma lem3382336 {A B : Type'} (h1 : term87 A B) (h2 : term89 A B) : term87 A B.
Proof. exact (@lem3382334 A B h2 (@lem3382335 A B h1)). Qed.
Lemma lem3382337 {A B : Type'} (h1 : term87 A B) : term90 A B.
Proof. exact (fun h0 : term89 A B => @lem3382336 A B h1 h0). Qed.
Lemma lem3382338 {A B : Type'} (h1 : term89 A B) : term89 A B.
Proof. exact (h1). Qed.
Lemma lem3382339 {A B : Type'} (h1 : term87 A B) (h2 : term89 A B) : term87 A B.
Proof. exact (@lem3382337 A B h1 (@lem3382338 A B h2)). Qed.
Lemma lem3382340 {A B : Type'} (h1 : term89 A B) : term89 A B.
Proof. exact (fun h0 : term87 A B => @lem3382339 A B h0 h1). Qed.
Lemma lem3382341 {A B : Type'} : term91 A B.
Proof. exact (fun h0 : term89 A B => @lem3382340 A B h0). Qed.
Lemma lem3382344 {A B : Type'} : term89 A B.
Proof. exact (@lem3382341 A B (@lem3382333 A B)). Qed.
Lemma lem3382345 {A B : Type'} : term89 A B.
Proof. exact (@lem3382344 A B). Qed.
Lemma lem3382347 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3382348 {A B : Type'} : (term87 A B) = (term92 A B).
Proof. exact (@lem3382347 (term88 A B)). Qed.
Lemma lem3382350 (t : Prop) : (term93 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3382351 {A B : Type'} : (term92 A B) = (term85 A B).
Proof. exact (@lem3382350 (term85 A B)). Qed.
Lemma lem3382478 {A B : Type'} : (term87 A B) = (term85 A B).
Proof. exact (TRANS (@lem3382348 A B) (@lem3382351 A B)). Qed.
Lemma lem3382481 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term74 A B x f a) = (term74 A B x f a).
Proof. exact (eq_refl (term74 A B x f a)). Qed.
Lemma lem3382486 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term68 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term68 A B x f s x')). Qed.
Lemma lem3382487 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3382486 A B x f s x')). Qed.
Lemma lem3382488 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382489 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3382488 A) (@lem3382487 A B x f s)). Qed.
Lemma lem3382490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382491 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term73 A B x f s) = (term73 A B x f s).
Proof. exact (MK_COMB (@lem3382490) (@lem3382489 A B x f s)). Qed.
Lemma lem3382492 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term75 A B s x f a) = (term75 A B s x f a).
Proof. exact (MK_COMB (@lem3382491 A B x f s) (@lem3382481 A B x f a)). Qed.
Lemma lem3382503 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term59 A B x f s x' a) = (term59 A B x f s x' a).
Proof. exact (eq_refl (term59 A B x f s x' a)). Qed.
Lemma lem3382504 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term61 A B x f s a) = (term61 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3382503 A B x f s x' a)). Qed.
Lemma lem3382505 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382506 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term62 A B x f s a) = (term62 A B x f s a).
Proof. exact (MK_COMB (@lem3382505 A) (@lem3382504 A B x f s a)). Qed.
Lemma lem3382507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3382508 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term64 A B x f s a) = (term64 A B x f s a).
Proof. exact (MK_COMB (@lem3382507) (@lem3382506 A B x f s a)). Qed.
Lemma lem3382509 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term62 A B x f s a) = (term75 A B s x f a)) = ((term62 A B x f s a) = (term75 A B s x f a)).
Proof. exact (MK_COMB (@lem3382508 A B x f s a) (@lem3382492 A B s x f a)). Qed.
Lemma lem3382510 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term77 A B s f a) = (term77 A B s f a).
Proof. exact (fun_ext (fun x : B => @lem3382509 A B s x f a)). Qed.
Lemma lem3382511 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3382512 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term78 A B s f a) = (term78 A B s f a).
Proof. exact (MK_COMB (@lem3382511 B) (@lem3382510 A B s f a)). Qed.
Lemma lem3382513 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3382526 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term35 A B s f x y) = (term35 A B s f x y).
Proof. exact (eq_refl (term35 A B s f x y)). Qed.
Lemma lem3382527 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term37 A B s f x) = (term37 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3382526 A B s f x y)). Qed.
Lemma lem3382528 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382529 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term39 A B s f x) = (term39 A B s f x).
Proof. exact (MK_COMB (@lem3382528 A) (@lem3382527 A B s f x)). Qed.
Lemma lem3382530 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term41 A B s f) = (term41 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3382529 A B s f x)). Qed.
Lemma lem3382531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382532 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term43 A B s f) = (term43 A B s f).
Proof. exact (MK_COMB (@lem3382531 A) (@lem3382530 A B s f)). Qed.
Lemma lem3382533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382534 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term45 A B s f) = (term45 A B s f).
Proof. exact (MK_COMB (@lem3382533) (@lem3382532 A B s f)). Qed.
Lemma lem3382535 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) : (term47 A B f s a) = (term47 A B f s a).
Proof. exact (MK_COMB (@lem3382534 A B s f) (@lem3382513 A s a)). Qed.
Lemma lem3382536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3382537 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) : (term48 A B f s a) = (term48 A B f s a).
Proof. exact (MK_COMB (@lem3382536) (@lem3382535 A B f s a)). Qed.
Lemma lem3382538 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term79 A B s f a) = (term79 A B s f a).
Proof. exact (MK_COMB (@lem3382537 A B f s a) (@lem3382512 A B s f a)). Qed.
Lemma lem3382539 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term80 A B s f) = (term80 A B s f).
Proof. exact (fun_ext (fun a : A => @lem3382538 A B s f a)). Qed.
Lemma lem3382540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382541 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term81 A B s f).
Proof. exact (MK_COMB (@lem3382540 A) (@lem3382539 A B s f)). Qed.
Lemma lem3382542 {A B : Type'} (f : A -> B) : (term82 A B f) = (term82 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3382541 A B s f)). Qed.
Lemma lem3382543 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3382544 {A B : Type'} (f : A -> B) : (term83 A B f) = (term83 A B f).
Proof. exact (MK_COMB (@lem3382543 A) (@lem3382542 A B f)). Qed.
Lemma lem3382545 {A B : Type'} : (term84 A B) = (term84 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3382544 A B f)). Qed.
Lemma lem3382546 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3382547 {A B : Type'} : (term85 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem3382546 A B) (@lem3382545 A B)). Qed.
Lemma lem3382616 {A B : Type'} : (term87 A B) = (term85 A B).
Proof. exact (TRANS (@lem3382478 A B) (@lem3382547 A B)). Qed.
Lemma lem3382617 {A B : Type'} : (term85 A B) = (term87 A B).
Proof. exact (SYM (@lem3382616 A B)). Qed.
Lemma lem3382618 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term47 A B f s a.
Proof. exact (h1). Qed.
Lemma lem3382620 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3382621 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term62 A B x f s a) = (term75 A B s x f a)) = (term94 A B s x f a).
Proof. exact (@lem3382620 ((term62 A B x f s a) = (term75 A B s x f a))). Qed.
Lemma lem3382622 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term94 A B s x f a) = ((term62 A B x f s a) = (term75 A B s x f a)).
Proof. exact (SYM (@lem3382621 A B s x f a)). Qed.
Lemma lem3382623 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term95 A B s x f a) : term95 A B s x f a.
Proof. exact (h1). Qed.
Lemma lem3382631 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term96 A B s x f y) = (term97 A B s x f y).
Proof. exact (@lem17045 (s y) ((f x) = (f y))). Qed.
Lemma lem3382633 {A : Type'} (s : A -> Prop) (x : A) : (term98 A s x) = (term98 A s x).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem3382634 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term99 A B s x f y) = (term100 A B s x f y).
Proof. exact (MK_COMB (@lem3382633 A s x) (@lem3382631 A B s x f y)). Qed.
Lemma lem3382635 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term101 A B s x f y) = (term99 A B s x f y).
Proof. exact (@lem17045 (s x) (term29 A B s x f y)). Qed.
Lemma lem3382636 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term101 A B s x f y) = (term100 A B s x f y).
Proof. exact (TRANS (@lem3382635 A B s x f y) (@lem3382634 A B s x f y)). Qed.
Lemma lem3382637 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3382638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3382639 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term102 A B s x f y) = (term103 A B s x f y).
Proof. exact (MK_COMB (@lem3382638) (@lem3382636 A B s x f y)). Qed.
Lemma lem3382640 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term104 A B s f x y) = (term105 A B s f x y).
Proof. exact (MK_COMB (@lem3382639 A B s x f y) (@lem3382637 A x y)). Qed.
Lemma lem3382641 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term35 A B s f x y) = (term104 A B s f x y).
Proof. exact (@lem17265 (term31 A B s x f y) (x = y)). Qed.
Lemma lem3382642 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term35 A B s f x y) = (term105 A B s f x y).
Proof. exact (TRANS (@lem3382641 A B s f x y) (@lem3382640 A B s f x y)). Qed.
Lemma lem3382643 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term37 A B s f x) = (term106 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3382642 A B s f x y)). Qed.
Lemma lem3382644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382645 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term39 A B s f x) = (term107 A B s f x).
Proof. exact (MK_COMB (@lem3382644 A) (@lem3382643 A B s f x)). Qed.
Lemma lem3382646 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term41 A B s f) = (term108 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3382645 A B s f x)). Qed.
Lemma lem3382647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382648 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term43 A B s f) = (term109 A B s f).
Proof. exact (MK_COMB (@lem3382647 A) (@lem3382646 A B s f)). Qed.
Lemma lem3382649 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3382650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382651 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term45 A B s f) = (term110 A B s f).
Proof. exact (MK_COMB (@lem3382650) (@lem3382648 A B s f)). Qed.
Lemma lem3382708 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) : (term47 A B f s a) = (term111 A B f s a).
Proof. exact (MK_COMB (@lem3382651 A B s f) (@lem3382649 A s a)). Qed.
Lemma lem3382709 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term111 A B f s a.
Proof. exact (EQ_MP (@lem3382708 A B f s a) (@lem3382618 A B f s a h1)). Qed.
Lemma lem3382717 {A : Type'} (x : A) (a : A) : (term112 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem3382719 {A : Type'} (s : A -> Prop) (x : A) : (term98 A s x) = (term98 A s x).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem3382720 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term113 A s x a) = (term114 A s x a).
Proof. exact (MK_COMB (@lem3382719 A s x) (@lem3382717 A x a)). Qed.
Lemma lem3382721 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term115 A s x a) = (term113 A s x a).
Proof. exact (@lem17045 (s x) (term55 A x a)). Qed.
Lemma lem3382722 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term115 A s x a) = (term114 A s x a).
Proof. exact (TRANS (@lem3382721 A s x a) (@lem3382720 A s x a)). Qed.
Lemma lem3382727 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term116 A B x f x') = (term116 A B x f x').
Proof. exact (eq_refl (term116 A B x f x')). Qed.
Lemma lem3382728 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term117 A B x f s x' a) = (term118 A B x f s x' a).
Proof. exact (MK_COMB (@lem3382727 A B x f x') (@lem3382722 A s x' a)). Qed.
Lemma lem3382729 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term119 A B x f s x' a) = (term117 A B x f s x' a).
Proof. exact (@lem17045 (x = (f x')) (term56 A s x' a)). Qed.
Lemma lem3382730 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term119 A B x f s x' a) = (term118 A B x f s x' a).
Proof. exact (TRANS (@lem3382729 A B x f s x' a) (@lem3382728 A B x f s x' a)). Qed.
Lemma lem3382733 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term59 A B x f s x' a) = (term59 A B x f s x' a).
Proof. exact (eq_refl (term59 A B x f s x' a)). Qed.
Lemma lem3382734 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3382735 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term122 A B x f s a) = (term123 A B x f s a).
Proof. exact (@lem3382734 A (term61 A B x f s a)). Qed.
Lemma lem3382736 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term124 A B x f s a x') = (term59 A B x f s x' a).
Proof. exact (eq_refl (term124 A B x f s a x')). Qed.
Lemma lem3382737 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3382738 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term125 A B x f s a x') = (term119 A B x f s x' a).
Proof. exact (MK_COMB (@lem3382737) (@lem3382736 A B x f s x' a)). Qed.
Lemma lem3382739 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term125 A B x f s a x') = (term118 A B x f s x' a).
Proof. exact (TRANS (@lem3382738 A B x f s x' a) (@lem3382730 A B x f s x' a)). Qed.
Lemma lem3382740 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term126 A B x f s a) = (term127 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3382739 A B x f s x' a)). Qed.
Lemma lem3382741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382742 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term123 A B x f s a) = (term128 A B x f s a).
Proof. exact (MK_COMB (@lem3382741 A) (@lem3382740 A B x f s a)). Qed.
Lemma lem3382743 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term122 A B x f s a) = (term128 A B x f s a).
Proof. exact (TRANS (@lem3382735 A B x f s a) (@lem3382742 A B x f s a)). Qed.
Lemma lem3382744 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term61 A B x f s a) = (term61 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3382733 A B x f s x' a)). Qed.
Lemma lem3382745 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382746 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term62 A B x f s a) = (term62 A B x f s a).
Proof. exact (MK_COMB (@lem3382745 A) (@lem3382744 A B x f s a)). Qed.
Lemma lem3382755 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term129 A B x f s x') = (term130 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3382758 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term68 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term68 A B x f s x')). Qed.
Lemma lem3382759 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3382760 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term132 A B x f s).
Proof. exact (@lem3382759 A (term70 A B x f s)). Qed.
Lemma lem3382761 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term133 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term133 A B x f s x')). Qed.
Lemma lem3382762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3382763 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term134 A B x f s x') = (term129 A B x f s x').
Proof. exact (MK_COMB (@lem3382762) (@lem3382761 A B x f s x')). Qed.
Lemma lem3382764 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term134 A B x f s x') = (term130 A B x f s x').
Proof. exact (TRANS (@lem3382763 A B x f s x') (@lem3382755 A B x f s x')). Qed.
Lemma lem3382765 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term136 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3382764 A B x f s x')). Qed.
Lemma lem3382766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3382767 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term137 A B x f s).
Proof. exact (MK_COMB (@lem3382766 A) (@lem3382765 A B x f s)). Qed.
Lemma lem3382768 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term137 A B x f s).
Proof. exact (TRANS (@lem3382760 A B x f s) (@lem3382767 A B x f s)). Qed.
Lemma lem3382769 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3382758 A B x f s x')). Qed.
Lemma lem3382770 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382771 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3382770 A) (@lem3382769 A B x f s)). Qed.
Lemma lem3382772 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term74 A B x f a) = (term74 A B x f a).
Proof. exact (eq_refl (term74 A B x f a)). Qed.
Lemma lem3382775 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term138 A B x f a) = (x = (f a)).
Proof. exact (@lem16933 (x = (f a))). Qed.
Lemma lem3382776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3382777 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term139 A B x f s) = (term140 A B x f s).
Proof. exact (MK_COMB (@lem3382776) (@lem3382768 A B x f s)). Qed.
Lemma lem3382778 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term141 A B s x f a) = (term142 A B s x f a).
Proof. exact (MK_COMB (@lem3382777 A B x f s) (@lem3382775 A B x f a)). Qed.
Lemma lem3382779 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term143 A B s x f a) = (term141 A B s x f a).
Proof. exact (@lem17045 (term71 A B x f s) (term74 A B x f a)). Qed.
Lemma lem3382780 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term143 A B s x f a) = (term142 A B s x f a).
Proof. exact (TRANS (@lem3382779 A B s x f a) (@lem3382778 A B s x f a)). Qed.
Lemma lem3382781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382782 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term73 A B x f s) = (term73 A B x f s).
Proof. exact (MK_COMB (@lem3382781) (@lem3382771 A B x f s)). Qed.
Lemma lem3382783 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term75 A B s x f a) = (term75 A B s x f a).
Proof. exact (MK_COMB (@lem3382782 A B x f s) (@lem3382772 A B x f a)). Qed.
Lemma lem3382784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382785 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term144 A B x f s a) = (term145 A B x f s a).
Proof. exact (MK_COMB (@lem3382784) (@lem3382743 A B x f s a)). Qed.
Lemma lem3382786 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term146 A B s x f a) = (term147 A B s x f a).
Proof. exact (MK_COMB (@lem3382785 A B x f s a) (@lem3382783 A B s x f a)). Qed.
Lemma lem3382787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382788 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term148 A B x f s a) = (term148 A B x f s a).
Proof. exact (MK_COMB (@lem3382787) (@lem3382746 A B x f s a)). Qed.
Lemma lem3382789 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term149 A B s x f a) = (term150 A B s x f a).
Proof. exact (MK_COMB (@lem3382788 A B x f s a) (@lem3382780 A B s x f a)). Qed.
Lemma lem3382790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3382791 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term151 A B s x f a) = (term152 A B s x f a).
Proof. exact (MK_COMB (@lem3382790) (@lem3382789 A B s x f a)). Qed.
Lemma lem3382792 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term153 A B s x f a) = (term154 A B s x f a).
Proof. exact (MK_COMB (@lem3382791 A B s x f a) (@lem3382786 A B s x f a)). Qed.
Lemma lem3382793 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term95 A B s x f a) = (term153 A B s x f a).
Proof. exact (@lem17646 (term62 A B x f s a) (term75 A B s x f a)). Qed.
Lemma lem3382794 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term95 A B s x f a) = (term154 A B s x f a).
Proof. exact (TRANS (@lem3382793 A B s x f a) (@lem3382792 A B s x f a)). Qed.
Lemma lem3382973 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3382974 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (@lem3382973 A P Q). Qed.
Lemma lem3382975 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term157 A B s x f a) = (term158 A B s x f a).
Proof. exact (@lem3382974 A (term61 A B x f s a) (term142 A B s x f a)). Qed.
Lemma lem3382976 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term124 A B x f s a x') = (term59 A B x f s x' a).
Proof. exact (eq_refl (term124 A B x f s a x')). Qed.
Lemma lem3382977 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term159 A B x f s a) = (term61 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3382976 A B x f s x' a)). Qed.
Lemma lem3382978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382979 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term160 A B x f s a) = (term62 A B x f s a).
Proof. exact (MK_COMB (@lem3382978 A) (@lem3382977 A B x f s a)). Qed.
Lemma lem3382980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382981 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term161 A B x f s a) = (term148 A B x f s a).
Proof. exact (MK_COMB (@lem3382980) (@lem3382979 A B x f s a)). Qed.
Lemma lem3382982 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term142 A B s x f a) = (term142 A B s x f a).
Proof. exact (eq_refl (term142 A B s x f a)). Qed.
Lemma lem3382983 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term157 A B s x f a) = (term150 A B s x f a).
Proof. exact (MK_COMB (@lem3382981 A B x f s a) (@lem3382982 A B s x f a)). Qed.
Lemma lem3382984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3382985 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term162 A B s x f a) = (term163 A B s x f a).
Proof. exact (MK_COMB (@lem3382984) (@lem3382983 A B s x f a)). Qed.
Lemma lem3382986 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term124 A B x f s a x') = (term59 A B x f s x' a).
Proof. exact (eq_refl (term124 A B x f s a x')). Qed.
Lemma lem3382987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3382988 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term164 A B x f s a x') = (term165 A B x f s x' a).
Proof. exact (MK_COMB (@lem3382987) (@lem3382986 A B x f s x' a)). Qed.
Lemma lem3382989 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term142 A B s x f a) = (term142 A B s x f a).
Proof. exact (eq_refl (term142 A B s x f a)). Qed.
Lemma lem3382990 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term166 A B x s x' f a) = (term167 A B x s x' f a).
Proof. exact (MK_COMB (@lem3382988 A B x' f s x a) (@lem3382989 A B s x' f a)). Qed.
Lemma lem3382991 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term168 A B s x f a) = (term169 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3382990 A B x' s x f a)). Qed.
Lemma lem3382992 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3382993 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term158 A B s x f a) = (term170 A B s x f a).
Proof. exact (MK_COMB (@lem3382992 A) (@lem3382991 A B s x f a)). Qed.
Lemma lem3382994 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term157 A B s x f a) = (term158 A B s x f a)) = ((term150 A B s x f a) = (term170 A B s x f a)).
Proof. exact (MK_COMB (@lem3382985 A B s x f a) (@lem3382993 A B s x f a)). Qed.
Lemma lem3382995 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term150 A B s x f a) = (term170 A B s x f a).
Proof. exact (EQ_MP (@lem3382994 A B s x f a) (@lem3382975 A B s x f a)). Qed.
Lemma lem3382996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3382997 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term152 A B s x f a) = (term171 A B s x f a).
Proof. exact (MK_COMB (@lem3382996) (@lem3382995 A B s x f a)). Qed.
Lemma lem3382999 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3383000 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (@lem3382999 A P Q). Qed.
Lemma lem3383001 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term172 A B s x f a) = (term173 A B s x f a).
Proof. exact (@lem3383000 A (term70 A B x f s) (term74 A B x f a)). Qed.
Lemma lem3383002 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term133 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term133 A B x f s x')). Qed.
Lemma lem3383003 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term174 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3383002 A B x f s x')). Qed.
Lemma lem3383004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383005 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term175 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3383004 A) (@lem3383003 A B x f s)). Qed.
Lemma lem3383006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3383007 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term176 A B x f s) = (term73 A B x f s).
Proof. exact (MK_COMB (@lem3383006) (@lem3383005 A B x f s)). Qed.
Lemma lem3383008 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term74 A B x f a) = (term74 A B x f a).
Proof. exact (eq_refl (term74 A B x f a)). Qed.
Lemma lem3383009 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term172 A B s x f a) = (term75 A B s x f a).
Proof. exact (MK_COMB (@lem3383007 A B x f s) (@lem3383008 A B x f a)). Qed.
Lemma lem3383010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383011 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term177 A B s x f a) = (term178 A B s x f a).
Proof. exact (MK_COMB (@lem3383010) (@lem3383009 A B s x f a)). Qed.
Lemma lem3383012 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term133 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term133 A B x f s x')). Qed.
Lemma lem3383013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3383014 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term179 A B x f s x') = (term180 A B x f s x').
Proof. exact (MK_COMB (@lem3383013) (@lem3383012 A B x f s x')). Qed.
Lemma lem3383015 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term74 A B x f a) = (term74 A B x f a).
Proof. exact (eq_refl (term74 A B x f a)). Qed.
Lemma lem3383016 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term181 A B s x x' f a) = (term182 A B s x x' f a).
Proof. exact (MK_COMB (@lem3383014 A B x' f s x) (@lem3383015 A B x' f a)). Qed.
Lemma lem3383017 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term183 A B s x f a) = (term184 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3383016 A B s x' x f a)). Qed.
Lemma lem3383018 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383019 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term173 A B s x f a) = (term185 A B s x f a).
Proof. exact (MK_COMB (@lem3383018 A) (@lem3383017 A B s x f a)). Qed.
Lemma lem3383020 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term172 A B s x f a) = (term173 A B s x f a)) = ((term75 A B s x f a) = (term185 A B s x f a)).
Proof. exact (MK_COMB (@lem3383011 A B s x f a) (@lem3383019 A B s x f a)). Qed.
Lemma lem3383021 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term75 A B s x f a) = (term185 A B s x f a).
Proof. exact (EQ_MP (@lem3383020 A B s x f a) (@lem3383001 A B s x f a)). Qed.
Lemma lem3383022 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term145 A B x f s a) = (term145 A B x f s a).
Proof. exact (eq_refl (term145 A B x f s a)). Qed.
Lemma lem3383023 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term147 A B s x f a) = (term186 A B s x f a).
Proof. exact (MK_COMB (@lem3383022 A B x f s a) (@lem3383021 A B s x f a)). Qed.
Lemma lem3383025 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3383026 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (@lem3383025 A P Q). Qed.
Lemma lem3383027 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term189 A B s x f a) = (term190 A B s x f a).
Proof. exact (@lem3383026 A (term128 A B x f s a) (term184 A B s x f a)). Qed.
Lemma lem3383028 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term191 A B s x' f a x) = (term182 A B s x x' f a).
Proof. exact (eq_refl (term191 A B s x' f a x)). Qed.
Lemma lem3383029 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term192 A B s x f a) = (term184 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3383028 A B s x' x f a)). Qed.
Lemma lem3383030 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383031 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term193 A B s x f a) = (term185 A B s x f a).
Proof. exact (MK_COMB (@lem3383030 A) (@lem3383029 A B s x f a)). Qed.
Lemma lem3383032 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term145 A B x f s a) = (term145 A B x f s a).
Proof. exact (eq_refl (term145 A B x f s a)). Qed.
Lemma lem3383033 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term189 A B s x f a) = (term186 A B s x f a).
Proof. exact (MK_COMB (@lem3383032 A B x f s a) (@lem3383031 A B s x f a)). Qed.
Lemma lem3383034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383035 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term194 A B s x f a) = (term195 A B s x f a).
Proof. exact (MK_COMB (@lem3383034) (@lem3383033 A B s x f a)). Qed.
Lemma lem3383036 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term191 A B s x' f a x) = (term182 A B s x x' f a).
Proof. exact (eq_refl (term191 A B s x' f a x)). Qed.
Lemma lem3383037 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term145 A B x f s a) = (term145 A B x f s a).
Proof. exact (eq_refl (term145 A B x f s a)). Qed.
Lemma lem3383038 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term196 A B s x' f a x) = (term197 A B s x x' f a).
Proof. exact (MK_COMB (@lem3383037 A B x' f s a) (@lem3383036 A B s x x' f a)). Qed.
Lemma lem3383039 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term198 A B s x f a) = (term199 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3383038 A B s x' x f a)). Qed.
Lemma lem3383040 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383041 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term190 A B s x f a) = (term200 A B s x f a).
Proof. exact (MK_COMB (@lem3383040 A) (@lem3383039 A B s x f a)). Qed.
Lemma lem3383042 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term189 A B s x f a) = (term190 A B s x f a)) = ((term186 A B s x f a) = (term200 A B s x f a)).
Proof. exact (MK_COMB (@lem3383035 A B s x f a) (@lem3383041 A B s x f a)). Qed.
Lemma lem3383043 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term186 A B s x f a) = (term200 A B s x f a).
Proof. exact (EQ_MP (@lem3383042 A B s x f a) (@lem3383027 A B s x f a)). Qed.
Lemma lem3383044 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term147 A B s x f a) = (term200 A B s x f a).
Proof. exact (TRANS (@lem3383023 A B s x f a) (@lem3383043 A B s x f a)). Qed.
Lemma lem3383045 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term154 A B s x f a) = (term201 A B s x f a).
Proof. exact (MK_COMB (@lem3382997 A B s x f a) (@lem3383044 A B s x f a)). Qed.
Lemma lem3383047 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term202 A P Q) = (term203 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3383048 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term202 A P Q) = (term203 A P Q).
Proof. exact (@lem3383047 A P Q). Qed.
Lemma lem3383049 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term204 A B s x f a) = (term205 A B s x f a).
Proof. exact (@lem3383048 A (term169 A B s x f a) (term199 A B s x f a)). Qed.
Lemma lem3383050 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term206 A B s x' f a x) = (term167 A B x s x' f a).
Proof. exact (eq_refl (term206 A B s x' f a x)). Qed.
Lemma lem3383051 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term207 A B s x f a) = (term169 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3383050 A B x' s x f a)). Qed.
Lemma lem3383052 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383053 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term208 A B s x f a) = (term170 A B s x f a).
Proof. exact (MK_COMB (@lem3383052 A) (@lem3383051 A B s x f a)). Qed.
Lemma lem3383054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3383055 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term209 A B s x f a) = (term171 A B s x f a).
Proof. exact (MK_COMB (@lem3383054) (@lem3383053 A B s x f a)). Qed.
Lemma lem3383056 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term210 A B s x' f a x) = (term197 A B s x x' f a).
Proof. exact (eq_refl (term210 A B s x' f a x)). Qed.
Lemma lem3383057 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term211 A B s x f a) = (term199 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3383056 A B s x' x f a)). Qed.
Lemma lem3383058 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383059 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term212 A B s x f a) = (term200 A B s x f a).
Proof. exact (MK_COMB (@lem3383058 A) (@lem3383057 A B s x f a)). Qed.
Lemma lem3383060 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term204 A B s x f a) = (term201 A B s x f a).
Proof. exact (MK_COMB (@lem3383055 A B s x f a) (@lem3383059 A B s x f a)). Qed.
Lemma lem3383061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383062 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term213 A B s x f a) = (term214 A B s x f a).
Proof. exact (MK_COMB (@lem3383061) (@lem3383060 A B s x f a)). Qed.
Lemma lem3383063 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term206 A B s x' f a x) = (term167 A B x s x' f a).
Proof. exact (eq_refl (term206 A B s x' f a x)). Qed.
Lemma lem3383064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3383065 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term215 A B s x' f a x) = (term216 A B x s x' f a).
Proof. exact (MK_COMB (@lem3383064) (@lem3383063 A B x s x' f a)). Qed.
Lemma lem3383066 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term210 A B s x' f a x) = (term197 A B s x x' f a).
Proof. exact (eq_refl (term210 A B s x' f a x)). Qed.
Lemma lem3383067 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term217 A B s x' f a x) = (term218 A B s x x' f a).
Proof. exact (MK_COMB (@lem3383065 A B x s x' f a) (@lem3383066 A B s x x' f a)). Qed.
Lemma lem3383068 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term219 A B s x f a) = (term220 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3383067 A B s x' x f a)). Qed.
Lemma lem3383069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3383070 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term205 A B s x f a) = (term221 A B s x f a).
Proof. exact (MK_COMB (@lem3383069 A) (@lem3383068 A B s x f a)). Qed.
Lemma lem3383071 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term204 A B s x f a) = (term205 A B s x f a)) = ((term201 A B s x f a) = (term221 A B s x f a)).
Proof. exact (MK_COMB (@lem3383062 A B s x f a) (@lem3383070 A B s x f a)). Qed.
Lemma lem3383072 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term201 A B s x f a) = (term221 A B s x f a).
Proof. exact (EQ_MP (@lem3383071 A B s x f a) (@lem3383049 A B s x f a)). Qed.
Lemma lem3383074 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term154 A B s x f a) = (term221 A B s x f a).
Proof. exact (TRANS (@lem3383045 A B s x f a) (@lem3383072 A B s x f a)). Qed.
Lemma lem3383075 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term95 A B s x f a) = (term221 A B s x f a).
Proof. exact (TRANS (@lem3382794 A B s x f a) (@lem3383074 A B s x f a)). Qed.
Lemma lem3383076 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term95 A B s x f a) : term221 A B s x f a.
Proof. exact (EQ_MP (@lem3383075 A B s x f a) (@lem3382623 A B s x f a h1)). Qed.
Lemma lem3383077 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term218 A B s x' x f a) : term218 A B s x' x f a.
Proof. exact (h1). Qed.
Lemma lem3383080 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem3383115 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term105 A B s f x y) = (term105 A B s f x y).
Proof. exact (eq_refl (term105 A B s f x y)). Qed.
Lemma lem3383116 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term106 A B s f x) = (term106 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3383115 A B s f x y)). Qed.
Lemma lem3383117 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383118 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B s f x) = (term107 A B s f x).
Proof. exact (MK_COMB (@lem3383117 A) (@lem3383116 A B s f x)). Qed.
Lemma lem3383119 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term108 A B s f) = (term108 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3383118 A B s f x)). Qed.
Lemma lem3383120 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383121 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term109 A B s f) = (term109 A B s f).
Proof. exact (MK_COMB (@lem3383120 A) (@lem3383119 A B s f)). Qed.
Lemma lem3383122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3383123 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term110 A B s f) = (term110 A B s f).
Proof. exact (MK_COMB (@lem3383122) (@lem3383121 A B s f)). Qed.
Lemma lem3383124 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) : (term111 A B f s a) = (term111 A B f s a).
Proof. exact (MK_COMB (@lem3383123 A B s f) (@lem3383080 A s a)). Qed.
Lemma lem3383125 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term111 A B f s a.
Proof. exact (EQ_MP (@lem3383124 A B f s a) (@lem3382709 A B f s a h1)). Qed.
Lemma lem3383150 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) : (term182 A B s x' x f a) = (term182 A B s x' x f a).
Proof. exact (eq_refl (term182 A B s x' x f a)). Qed.
Lemma lem3383175 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term118 A B x f s x' a) = (term118 A B x f s x' a).
Proof. exact (eq_refl (term118 A B x f s x' a)). Qed.
Lemma lem3383176 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term127 A B x f s a) = (term127 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3383175 A B x f s x' a)). Qed.
Lemma lem3383177 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383178 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term128 A B x f s a) = (term128 A B x f s a).
Proof. exact (MK_COMB (@lem3383177 A) (@lem3383176 A B x f s a)). Qed.
Lemma lem3383179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3383180 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term145 A B x f s a) = (term145 A B x f s a).
Proof. exact (MK_COMB (@lem3383179) (@lem3383178 A B x f s a)). Qed.
Lemma lem3383181 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) : (term197 A B s x' x f a) = (term197 A B s x' x f a).
Proof. exact (MK_COMB (@lem3383180 A B x f s a) (@lem3383150 A B s x' x f a)). Qed.
Lemma lem3383188 {A B : Type'} (x : B) (f : A -> B) (a : A) : (x = (f a)) = (x = (f a)).
Proof. exact (eq_refl (x = (f a))). Qed.
Lemma lem3383205 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term130 A B x f s x') = (term130 A B x f s x').
Proof. exact (eq_refl (term130 A B x f s x')). Qed.
Lemma lem3383206 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term136 A B x f s) = (term136 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3383205 A B x f s x')). Qed.
Lemma lem3383207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383208 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term137 A B x f s) = (term137 A B x f s).
Proof. exact (MK_COMB (@lem3383207 A) (@lem3383206 A B x f s)). Qed.
Lemma lem3383209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3383210 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term140 A B x f s) = (term140 A B x f s).
Proof. exact (MK_COMB (@lem3383209) (@lem3383208 A B x f s)). Qed.
Lemma lem3383211 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term142 A B s x f a) = (term142 A B s x f a).
Proof. exact (MK_COMB (@lem3383210 A B x f s) (@lem3383188 A B x f a)). Qed.
Lemma lem3383236 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term165 A B x f s x' a) = (term165 A B x f s x' a).
Proof. exact (eq_refl (term165 A B x f s x' a)). Qed.
Lemma lem3383237 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term167 A B x' s x f a) = (term167 A B x' s x f a).
Proof. exact (MK_COMB (@lem3383236 A B x f s x' a) (@lem3383211 A B s x f a)). Qed.
Lemma lem3383238 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3383239 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term216 A B x' s x f a) = (term216 A B x' s x f a).
Proof. exact (MK_COMB (@lem3383238) (@lem3383237 A B x' s x f a)). Qed.
Lemma lem3383240 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) : (term218 A B s x' x f a) = (term218 A B s x' x f a).
Proof. exact (MK_COMB (@lem3383239 A B x' s x f a) (@lem3383181 A B s x' x f a)). Qed.
Lemma lem3383241 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term218 A B s x' x f a) : term218 A B s x' x f a.
Proof. exact (EQ_MP (@lem3383240 A B s x' x f a) (@lem3383077 A B s x' x f a h1)). Qed.
Lemma lem3383243 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term109 A B s f.
Proof. exact (proj1 (@lem3383125 A B f s a h1)). Qed.
Lemma lem3383244 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term167 A B x' s x f a.
Proof. exact (h1). Qed.
Lemma lem3383245 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term197 A B s x' x f a.
Proof. exact (h1). Qed.
Lemma lem3383246 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term142 A B s x f a.
Proof. exact (proj2 (@lem3383244 A B x' s x f a h1)). Qed.
Lemma lem3383247 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term59 A B x f s x' a.
Proof. exact (proj1 (@lem3383244 A B x' s x f a h1)). Qed.
Lemma lem3383248 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term56 A s x' a.
Proof. exact (proj2 (@lem3383247 A B x' s x f a h1)). Qed.
Lemma lem3383252 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term137 A B x f s) : term137 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3383254 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term182 A B s x' x f a.
Proof. exact (proj2 (@lem3383245 A B s x' x f a h1)). Qed.
Lemma lem3383255 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term128 A B x f s a.
Proof. exact (proj1 (@lem3383245 A B s x' x f a h1)). Qed.
Lemma lem3383257 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term68 A B x f s x'.
Proof. exact (proj1 (@lem3383254 A B s x' x f a h1)). Qed.
Lemma lem3383311 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term130 A B x f s x') = (term130 A B x f s x').
Proof. exact (eq_refl (term130 A B x f s x')). Qed.
Lemma lem3383312 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term136 A B x f s) = (term136 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3383311 A B x f s x')). Qed.
Lemma lem3383313 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383315 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term137 A B x f s) = (term137 A B x f s).
Proof. exact (MK_COMB (@lem3383313 A) (@lem3383312 A B x f s)). Qed.
Lemma lem3383316 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term137 A B x f s) : term137 A B x f s.
Proof. exact (EQ_MP (@lem3383315 A B x f s) (@lem3383252 A B x f s h1)). Qed.
Lemma lem3383336 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term105 A B s f x y) = (term105 A B s f x y).
Proof. exact (eq_refl (term105 A B s f x y)). Qed.
Lemma lem3383337 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term106 A B s f x) = (term106 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3383336 A B s f x y)). Qed.
Lemma lem3383338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383339 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B s f x) = (term107 A B s f x).
Proof. exact (MK_COMB (@lem3383338 A) (@lem3383337 A B s f x)). Qed.
Lemma lem3383340 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term108 A B s f) = (term108 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3383339 A B s f x)). Qed.
Lemma lem3383341 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383343 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term109 A B s f) = (term109 A B s f).
Proof. exact (MK_COMB (@lem3383341 A) (@lem3383340 A B s f)). Qed.
Lemma lem3383344 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term109 A B s f.
Proof. exact (EQ_MP (@lem3383343 A B s f) (@lem3383243 A B f s a h1)). Qed.
Lemma lem3383364 {A B : Type'} (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : x = (f a).
Proof. exact (h1). Qed.
Lemma lem3383410 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term118 A B x f s x' a) = (term118 A B x f s x' a).
Proof. exact (eq_refl (term118 A B x f s x' a)). Qed.
Lemma lem3383411 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term127 A B x f s a) = (term127 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3383410 A B x f s x' a)). Qed.
Lemma lem3383412 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3383414 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term128 A B x f s a) = (term128 A B x f s a).
Proof. exact (MK_COMB (@lem3383412 A) (@lem3383411 A B x f s a)). Qed.
Lemma lem3383415 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term128 A B x f s a.
Proof. exact (EQ_MP (@lem3383414 A B x f s a) (@lem3383255 A B s x' x f a h1)). Qed.
Lemma lem3383434 {A B : Type'} (_35495 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term137 A B x f s) : term222 A B x f s _35495.
Proof. exact (@lem3383316 A B x f s h1 _35495). Qed.
Lemma lem3383435 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term222 A B x f s _35495) = (term130 A B x f s _35495).
Proof. exact (eq_refl (term222 A B x f s _35495)). Qed.
Lemma lem3383437 {A B : Type'} (_35496 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term223 A B s f _35496.
Proof. exact (@lem3383344 A B f s a h1 _35496). Qed.
Lemma lem3383438 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) : (term223 A B s f _35496) = (term107 A B s f _35496).
Proof. exact (eq_refl (term223 A B s f _35496)). Qed.
Lemma lem3383439 {A B : Type'} (_35496 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term107 A B s f _35496.
Proof. exact (EQ_MP (@lem3383438 A B s f _35496) (@lem3383437 A B _35496 f s a h1)). Qed.
Lemma lem3383440 {A B : Type'} (_35496 : A) (_35497 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term224 A B s f _35496 _35497.
Proof. exact (@lem3383439 A B _35496 f s a h1 _35497). Qed.
Lemma lem3383441 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term224 A B s f _35496 _35497) = (term105 A B s f _35496 _35497).
Proof. exact (eq_refl (term224 A B s f _35496 _35497)). Qed.
Lemma lem3383442 {A B : Type'} (_35496 : A) (_35497 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term105 A B s f _35496 _35497.
Proof. exact (EQ_MP (@lem3383441 A B s f _35496 _35497) (@lem3383440 A B _35496 _35497 f s a h1)). Qed.
Lemma lem3383449 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term225 A B x f s a _35500.
Proof. exact (@lem3383415 A B s x' x f a h1 _35500). Qed.
Lemma lem3383450 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term225 A B x f s a _35500) = (term118 A B x f s _35500 a).
Proof. exact (eq_refl (term225 A B x f s a _35500)). Qed.
Lemma lem3383473 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : x = (f x').
Proof. exact (proj1 (@lem3383247 A B x' s x f a h1)). Qed.
Lemma lem3383483 {A B : Type'} (_35495 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term137 A B x f s) : term130 A B x f s _35495.
Proof. exact (EQ_MP (@lem3383435 A B x f s _35495) (@lem3383434 A B _35495 x f s h1)). Qed.
Lemma lem3383487 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term105 A B s f _35496 _35497) = (term226 A B s f _35496 _35497).
Proof. exact (@lem3382033 (term227 A s _35496) (term97 A B s _35496 f _35497) (_35496 = _35497)). Qed.
Lemma lem3383494 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term228 A B s f _35496 _35497) = (term229 A B s f _35496 _35497).
Proof. exact (@lem3382033 (term227 A s _35497) (term230 A B _35496 f _35497) (_35496 = _35497)). Qed.
Lemma lem3383495 {A : Type'} (s : A -> Prop) (_35496 : A) : (term98 A s _35496) = (term98 A s _35496).
Proof. exact (eq_refl (term98 A s _35496)). Qed.
Lemma lem3383498 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term226 A B s f _35496 _35497) = (term231 A B s f _35496 _35497).
Proof. exact (MK_COMB (@lem3383495 A s _35496) (@lem3383494 A B s f _35496 _35497)). Qed.
Lemma lem3383500 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term105 A B s f _35496 _35497) = (term231 A B s f _35496 _35497).
Proof. exact (TRANS (@lem3383487 A B s f _35496 _35497) (@lem3383498 A B s f _35496 _35497)). Qed.
Lemma lem3383505 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : x = (f x').
Proof. exact (proj1 (@lem3383247 A B x' s x f a h1)). Qed.
Lemma lem3383511 {A B : Type'} (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : x = (f a).
Proof. exact (h1). Qed.
Lemma lem3383541 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term118 A B x f s _35500 a.
Proof. exact (EQ_MP (@lem3383450 A B x f s _35500 a) (@lem3383449 A B _35500 s x' x f a h1)). Qed.
Lemma lem3383543 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term74 A B x f a.
Proof. exact (proj2 (@lem3383254 A B s x' x f a h1)). Qed.
Lemma lem3383545 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : x = (f x').
Proof. exact (proj1 (@lem3383257 A B s x' x f a h1)). Qed.
Lemma lem3383618 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35495 : A) : (term232 A B f s _35495) = (term232 A B f s _35495).
Proof. exact (eq_refl (term232 A B f s _35495)). Qed.
Lemma lem3383619 {A B : Type'} (_35495 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : (term233 A B f s _35495 x) = (term234 A B s _35495 f x').
Proof. exact (MK_COMB (@lem3383618 A B f s _35495) (@lem3383473 A B x' s x f a h1)). Qed.
Lemma lem3383620 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term234 A B s _35495 f x') = (term235 A B x' f s _35495).
Proof. exact (eq_refl (term234 A B s _35495 f x')). Qed.
Lemma lem3383621 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35495 : A) (x : B) : (term236 A B f s _35495 x) = (term236 A B f s _35495 x).
Proof. exact (eq_refl (term236 A B f s _35495 x)). Qed.
Lemma lem3383622 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : ((term233 A B f s _35495 x) = (term234 A B s _35495 f x')) = ((term233 A B f s _35495 x) = (term235 A B x' f s _35495)).
Proof. exact (MK_COMB (@lem3383621 A B f s _35495 x) (@lem3383620 A B x' f s _35495)). Qed.
Lemma lem3383623 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term233 A B f s _35495 x) = (term130 A B x f s _35495).
Proof. exact (eq_refl (term233 A B f s _35495 x)). Qed.
Lemma lem3383624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383625 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term236 A B f s _35495 x) = (term237 A B x f s _35495).
Proof. exact (MK_COMB (@lem3383624) (@lem3383623 A B x f s _35495)). Qed.
Lemma lem3383626 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term235 A B x' f s _35495) = (term235 A B x' f s _35495).
Proof. exact (eq_refl (term235 A B x' f s _35495)). Qed.
Lemma lem3383627 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : ((term233 A B f s _35495 x) = (term235 A B x' f s _35495)) = ((term130 A B x f s _35495) = (term235 A B x' f s _35495)).
Proof. exact (MK_COMB (@lem3383625 A B x f s _35495) (@lem3383626 A B x' f s _35495)). Qed.
Lemma lem3383628 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : ((term233 A B f s _35495 x) = (term234 A B s _35495 f x')) = ((term130 A B x f s _35495) = (term235 A B x' f s _35495)).
Proof. exact (TRANS (@lem3383622 A B x x' f s _35495) (@lem3383627 A B x x' f s _35495)). Qed.
Lemma lem3383629 {A B : Type'} (_35495 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : (term130 A B x f s _35495) = (term235 A B x' f s _35495).
Proof. exact (EQ_MP (@lem3383628 A B x x' f s _35495) (@lem3383619 A B _35495 x' s x f a h1)). Qed.
Lemma lem3383630 {A B : Type'} (_35495 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : term235 A B x' f s _35495.
Proof. exact (EQ_MP (@lem3383629 A B _35495 x' s x f a h2) (@lem3383483 A B _35495 x f s h1)). Qed.
Lemma lem3383658 {A B : Type'} (_35496 : A) (_35497 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term231 A B s f _35496 _35497.
Proof. exact (EQ_MP (@lem3383500 A B s f _35496 _35497) (@lem3383442 A B _35496 _35497 f s a h1)). Qed.
Lemma lem3383673 {A B : Type'} (f : A -> B) (x' : A) : (term238 A B f x') = (term238 A B f x').
Proof. exact (eq_refl (term238 A B f x')). Qed.
Lemma lem3383674 {A B : Type'} (x' : A) (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : (term239 A B f x' x) = (term240 A B x' f a).
Proof. exact (MK_COMB (@lem3383673 A B f x') (@lem3383511 A B x f a h1)). Qed.
Lemma lem3383675 {A B : Type'} (a : A) (f : A -> B) (x' : A) : (term240 A B x' f a) = ((f a) = (f x')).
Proof. exact (eq_refl (term240 A B x' f a)). Qed.
Lemma lem3383676 {A B : Type'} (f : A -> B) (x' : A) (x : B) : (term241 A B f x' x) = (term241 A B f x' x).
Proof. exact (eq_refl (term241 A B f x' x)). Qed.
Lemma lem3383677 {A B : Type'} (x : B) (a : A) (f : A -> B) (x' : A) : ((term239 A B f x' x) = (term240 A B x' f a)) = ((term239 A B f x' x) = ((f a) = (f x'))).
Proof. exact (MK_COMB (@lem3383676 A B f x' x) (@lem3383675 A B a f x')). Qed.
Lemma lem3383678 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term239 A B f x' x) = (x = (f x')).
Proof. exact (eq_refl (term239 A B f x' x)). Qed.
Lemma lem3383679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383680 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term241 A B f x' x) = (term242 A B x f x').
Proof. exact (MK_COMB (@lem3383679) (@lem3383678 A B x f x')). Qed.
Lemma lem3383681 {A B : Type'} (a : A) (f : A -> B) (x' : A) : ((f a) = (f x')) = ((f a) = (f x')).
Proof. exact (eq_refl ((f a) = (f x'))). Qed.
Lemma lem3383682 {A B : Type'} (x : B) (a : A) (f : A -> B) (x' : A) : ((term239 A B f x' x) = ((f a) = (f x'))) = ((x = (f x')) = ((f a) = (f x'))).
Proof. exact (MK_COMB (@lem3383680 A B x f x') (@lem3383681 A B a f x')). Qed.
Lemma lem3383683 {A B : Type'} (x : B) (a : A) (f : A -> B) (x' : A) : ((term239 A B f x' x) = (term240 A B x' f a)) = ((x = (f x')) = ((f a) = (f x'))).
Proof. exact (TRANS (@lem3383677 A B x a f x') (@lem3383682 A B x a f x')). Qed.
Lemma lem3383684 {A B : Type'} (x' : A) (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : (x = (f x')) = ((f a) = (f x')).
Proof. exact (EQ_MP (@lem3383683 A B x a f x') (@lem3383674 A B x' x f a h1)). Qed.
Lemma lem3383713 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term55 A x' a.
Proof. exact (proj2 (@lem3383248 A B x' s x f a h1)). Qed.
Lemma lem3383756 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term243 A B f s _35500 a) = (term243 A B f s _35500 a).
Proof. exact (eq_refl (term243 A B f s _35500 a)). Qed.
Lemma lem3383757 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : (term244 A B f s _35500 a x) = (term245 A B s _35500 a f x').
Proof. exact (MK_COMB (@lem3383756 A B f s _35500 a) (@lem3383545 A B s x' x f a h1)). Qed.
Lemma lem3383758 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term245 A B s _35500 a f x') = (term246 A B x' f s _35500 a).
Proof. exact (eq_refl (term245 A B s _35500 a f x')). Qed.
Lemma lem3383759 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) (x : B) : (term247 A B f s _35500 a x) = (term247 A B f s _35500 a x).
Proof. exact (eq_refl (term247 A B f s _35500 a x)). Qed.
Lemma lem3383760 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : ((term244 A B f s _35500 a x) = (term245 A B s _35500 a f x')) = ((term244 A B f s _35500 a x) = (term246 A B x' f s _35500 a)).
Proof. exact (MK_COMB (@lem3383759 A B f s _35500 a x) (@lem3383758 A B x' f s _35500 a)). Qed.
Lemma lem3383761 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term244 A B f s _35500 a x) = (term118 A B x f s _35500 a).
Proof. exact (eq_refl (term244 A B f s _35500 a x)). Qed.
Lemma lem3383762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383763 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term247 A B f s _35500 a x) = (term248 A B x f s _35500 a).
Proof. exact (MK_COMB (@lem3383762) (@lem3383761 A B x f s _35500 a)). Qed.
Lemma lem3383764 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term246 A B x' f s _35500 a) = (term246 A B x' f s _35500 a).
Proof. exact (eq_refl (term246 A B x' f s _35500 a)). Qed.
Lemma lem3383765 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : ((term244 A B f s _35500 a x) = (term246 A B x' f s _35500 a)) = ((term118 A B x f s _35500 a) = (term246 A B x' f s _35500 a)).
Proof. exact (MK_COMB (@lem3383763 A B x f s _35500 a) (@lem3383764 A B x' f s _35500 a)). Qed.
Lemma lem3383766 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : ((term244 A B f s _35500 a x) = (term245 A B s _35500 a f x')) = ((term118 A B x f s _35500 a) = (term246 A B x' f s _35500 a)).
Proof. exact (TRANS (@lem3383760 A B x x' f s _35500 a) (@lem3383765 A B x x' f s _35500 a)). Qed.
Lemma lem3383767 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : (term118 A B x f s _35500 a) = (term246 A B x' f s _35500 a).
Proof. exact (EQ_MP (@lem3383766 A B x x' f s _35500 a) (@lem3383757 A B _35500 s x' x f a h1)). Qed.
Lemma lem3383768 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term246 A B x' f s _35500 a.
Proof. exact (EQ_MP (@lem3383767 A B _35500 s x' x f a h1) (@lem3383541 A B _35500 s x' x f a h1)). Qed.
Lemma lem3383769 {A B : Type'} (f : A -> B) (a : A) : (term249 A B f a) = (term249 A B f a).
Proof. exact (eq_refl (term249 A B f a)). Qed.
Lemma lem3383770 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : (term250 A B f a x) = (term251 A B a f x').
Proof. exact (MK_COMB (@lem3383769 A B f a) (@lem3383545 A B s x' x f a h1)). Qed.
Lemma lem3383771 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term251 A B a f x') = (term230 A B x' f a).
Proof. exact (eq_refl (term251 A B a f x')). Qed.
Lemma lem3383772 {A B : Type'} (f : A -> B) (a : A) (x : B) : (term252 A B f a x) = (term252 A B f a x).
Proof. exact (eq_refl (term252 A B f a x)). Qed.
Lemma lem3383773 {A B : Type'} (x : B) (x' : A) (f : A -> B) (a : A) : ((term250 A B f a x) = (term251 A B a f x')) = ((term250 A B f a x) = (term230 A B x' f a)).
Proof. exact (MK_COMB (@lem3383772 A B f a x) (@lem3383771 A B x' f a)). Qed.
Lemma lem3383774 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term250 A B f a x) = (term74 A B x f a).
Proof. exact (eq_refl (term250 A B f a x)). Qed.
Lemma lem3383775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3383776 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term252 A B f a x) = (term253 A B x f a).
Proof. exact (MK_COMB (@lem3383775) (@lem3383774 A B x f a)). Qed.
Lemma lem3383777 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term230 A B x' f a) = (term230 A B x' f a).
Proof. exact (eq_refl (term230 A B x' f a)). Qed.
Lemma lem3383778 {A B : Type'} (x : B) (x' : A) (f : A -> B) (a : A) : ((term250 A B f a x) = (term230 A B x' f a)) = ((term74 A B x f a) = (term230 A B x' f a)).
Proof. exact (MK_COMB (@lem3383776 A B x f a) (@lem3383777 A B x' f a)). Qed.
Lemma lem3383779 {A B : Type'} (x : B) (x' : A) (f : A -> B) (a : A) : ((term250 A B f a x) = (term251 A B a f x')) = ((term74 A B x f a) = (term230 A B x' f a)).
Proof. exact (TRANS (@lem3383773 A B x x' f a) (@lem3383778 A B x x' f a)). Qed.
Lemma lem3383780 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : (term74 A B x f a) = (term230 A B x' f a).
Proof. exact (EQ_MP (@lem3383779 A B x x' f a) (@lem3383770 A B s x' x f a h1)). Qed.
Lemma lem3383781 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term230 A B x' f a.
Proof. exact (EQ_MP (@lem3383780 A B s x' x f a h1) (@lem3383543 A B s x' x f a h1)). Qed.
Lemma lem3383821 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3383822 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3383821 B x). Qed.
Lemma lem3383823 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3383822 B (f x')). Qed.
Lemma lem3383824 {A B : Type'} (f : A -> B) (x' : A) : term254 A B f x'.
Proof. exact (fun h0 : term255 A B f x' => @lem3383823 A B f x'). Qed.
Lemma lem3383826 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3383827 {A B : Type'} (f : A -> B) (x' : A) : (term254 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3383826 ((f x') = (f x'))). Qed.
Lemma lem3383828 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3383827 A B f x') (@lem3383824 A B f x')). Qed.
Lemma lem3383830 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : s x'.
Proof. exact (proj1 (@lem3383248 A B x' s x f a h1)). Qed.
Lemma lem3383831 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term257 A s x'.
Proof. exact (fun h0 : term227 A s x' => @lem3383830 A B x' s x f a h1). Qed.
Lemma lem3383833 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3383834 {A : Type'} (s : A -> Prop) (x' : A) : (term257 A s x') = (s x').
Proof. exact (@lem3383833 (s x')). Qed.
Lemma lem3383835 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : s x'.
Proof. exact (EQ_MP (@lem3383834 A s x') (@lem3383831 A B x' s x f a h1)). Qed.
Lemma lem3383837 (a : Prop) (b : Prop) : (term258 a b) = (term259 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3383838 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term235 A B x' f s _35495) = (term260 A B x' f s _35495).
Proof. exact (@lem3383837 ((f x') = (f _35495)) (s _35495)). Qed.
Lemma lem3383840 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3383841 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term260 A B x' f s _35495) = (term261 A B x' f s _35495).
Proof. exact (@lem3383840 (term262 A B x' f s _35495)). Qed.
Lemma lem3383842 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35495 : A) : (term235 A B x' f s _35495) = (term261 A B x' f s _35495).
Proof. exact (TRANS (@lem3383838 A B x' f s _35495) (@lem3383841 A B x' f s _35495)). Qed.
Lemma lem3383844 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term263 A B f s x'.
Proof. exact (conj (@lem3383828 A B f x') (@lem3383835 A B x' s x f a h1)). Qed.
Lemma lem3383846 {A B : Type'} (_35495 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : term261 A B x' f s _35495.
Proof. exact (EQ_MP (@lem3383842 A B x' f s _35495) (@lem3383630 A B _35495 x' s x f a h1 h2)). Qed.
Lemma lem3383847 {A B : Type'} (_35495 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : term261 A B x' f s _35495.
Proof. exact (@lem3383846 A B _35495 x' s x f a h1 h2). Qed.
Lemma lem3383848 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : term264 A B f s x'.
Proof. exact (@lem3383847 A B x' x' s x f a h1 h2). Qed.
Lemma lem3383851 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : False.
Proof. exact (@lem3383848 A B x' s x f a h1 h2 (@lem3383844 A B x' s x f a h2)). Qed.
Lemma lem3383852 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : term265.
Proof. exact (fun h0 : ~ False => @lem3383851 A B x' s x f a h1 h2). Qed.
Lemma lem3383854 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3383855 : term265 = False.
Proof. exact (@lem3383854 False). Qed.
Lemma lem3383880 {A : Type'} (x : A) (y : A) (z : A) : term266 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3383882 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : s a.
Proof. exact (proj2 (@lem3383125 A B f s a h1)). Qed.
Lemma lem3383883 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term257 A s a.
Proof. exact (fun h0 : term227 A s a => @lem3383882 A B f s a h1). Qed.
Lemma lem3383885 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3383886 {A : Type'} (s : A -> Prop) (a : A) : (term257 A s a) = (s a).
Proof. exact (@lem3383885 (s a)). Qed.
Lemma lem3383887 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : s a.
Proof. exact (EQ_MP (@lem3383886 A s a) (@lem3383883 A B f s a h1)). Qed.
Lemma lem3383889 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : s x'.
Proof. exact (proj1 (@lem3383248 A B x' s x f a h1)). Qed.
Lemma lem3383890 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term257 A s x'.
Proof. exact (fun h0 : term227 A s x' => @lem3383889 A B x' s x f a h1). Qed.
Lemma lem3383892 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3383893 {A : Type'} (s : A -> Prop) (x' : A) : (term257 A s x') = (s x').
Proof. exact (@lem3383892 (s x')). Qed.
Lemma lem3383894 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : s x'.
Proof. exact (EQ_MP (@lem3383893 A s x') (@lem3383890 A B x' s x f a h1)). Qed.
Lemma lem3383896 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) (h2 : x = (f a)) : (f a) = (f x').
Proof. exact (EQ_MP (@lem3383684 A B x' x f a h2) (@lem3383505 A B x' s x f a h1)). Qed.
Lemma lem3383897 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) (h2 : x = (f a)) : term267 A B a f x'.
Proof. exact (fun h0 : term230 A B a f x' => @lem3383896 A B x' s x f a h1 h2). Qed.
Lemma lem3383899 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3383900 {A B : Type'} (a : A) (f : A -> B) (x' : A) : (term267 A B a f x') = ((f a) = (f x')).
Proof. exact (@lem3383899 ((f a) = (f x'))). Qed.
Lemma lem3383901 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) (h2 : x = (f a)) : (f a) = (f x').
Proof. exact (EQ_MP (@lem3383900 A B a f x') (@lem3383897 A B x' s x f a h1 h2)). Qed.
Lemma lem3383927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3383928 {A B : Type'} (_35496 : A) (f : A -> B) (_35497 : A) : (term268 A B f _35496 _35497) = (term269 A B _35496 f _35497).
Proof. exact (@lem3383927 (_35496 = _35497) (term230 A B _35496 f _35497)). Qed.
Lemma lem3383938 {A : Type'} (s : A -> Prop) (_35497 : A) : (term98 A s _35497) = (term98 A s _35497).
Proof. exact (eq_refl (term98 A s _35497)). Qed.
Lemma lem3383939 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term229 A B s f _35496 _35497) = (term270 A B s _35496 f _35497).
Proof. exact (MK_COMB (@lem3383938 A s _35497) (@lem3383928 A B _35496 f _35497)). Qed.
Lemma lem3383943 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3383944 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term270 A B s _35496 f _35497) = (term271 A B s _35496 f _35497).
Proof. exact (@lem3383943 (_35496 = _35497) (term227 A s _35497) (term230 A B _35496 f _35497)). Qed.
Lemma lem3383964 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term229 A B s f _35496 _35497) = (term271 A B s _35496 f _35497).
Proof. exact (TRANS (@lem3383939 A B s _35496 f _35497) (@lem3383944 A B s _35496 f _35497)). Qed.
Lemma lem3383965 {A : Type'} (s : A -> Prop) (_35496 : A) : (term98 A s _35496) = (term98 A s _35496).
Proof. exact (eq_refl (term98 A s _35496)). Qed.
Lemma lem3383966 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term231 A B s f _35496 _35497) = (term272 A B s _35496 f _35497).
Proof. exact (MK_COMB (@lem3383965 A s _35496) (@lem3383964 A B s _35496 f _35497)). Qed.
Lemma lem3383970 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3383971 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term272 A B s _35496 f _35497) = (term273 A B s _35496 f _35497).
Proof. exact (@lem3383970 (_35496 = _35497) (term227 A s _35496) (term97 A B s _35496 f _35497)). Qed.
Lemma lem3384001 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term231 A B s f _35496 _35497) = (term273 A B s _35496 f _35497).
Proof. exact (TRANS (@lem3383966 A B s _35496 f _35497) (@lem3383971 A B s _35496 f _35497)). Qed.
Lemma lem3384002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384003 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term274 A B s f _35496 _35497) = (term275 A B s _35496 f _35497).
Proof. exact (MK_COMB (@lem3384002) (@lem3384001 A B s _35496 f _35497)). Qed.
Lemma lem3384033 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term273 A B s _35496 f _35497) = (term273 A B s _35496 f _35497).
Proof. exact (eq_refl (term273 A B s _35496 f _35497)). Qed.
Lemma lem3384034 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : ((term231 A B s f _35496 _35497) = (term273 A B s _35496 f _35497)) = ((term273 A B s _35496 f _35497) = (term273 A B s _35496 f _35497)).
Proof. exact (MK_COMB (@lem3384003 A B s _35496 f _35497) (@lem3384033 A B s _35496 f _35497)). Qed.
Lemma lem3384036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3384037 (x : Prop) : (x = x) = True.
Proof. exact (@lem3384036 Prop x). Qed.
Lemma lem3384038 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : ((term273 A B s _35496 f _35497) = (term273 A B s _35496 f _35497)) = True.
Proof. exact (@lem3384037 (term273 A B s _35496 f _35497)). Qed.
Lemma lem3384039 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : ((term231 A B s f _35496 _35497) = (term273 A B s _35496 f _35497)) = True.
Proof. exact (TRANS (@lem3384034 A B s _35496 f _35497) (@lem3384038 A B s _35496 f _35497)). Qed.
Lemma lem3384040 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : True = ((term231 A B s f _35496 _35497) = (term273 A B s _35496 f _35497)).
Proof. exact (SYM (@lem3384039 A B s _35496 f _35497)). Qed.
Lemma lem3384041 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term231 A B s f _35496 _35497) = (term273 A B s _35496 f _35497).
Proof. exact (EQ_MP (@lem3384040 A B s _35496 f _35497) (@lem0)). Qed.
Lemma lem3384042 {A B : Type'} (_35496 : A) (_35497 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term273 A B s _35496 f _35497.
Proof. exact (EQ_MP (@lem3384041 A B s _35496 f _35497) (@lem3383658 A B _35496 _35497 f s a h1)). Qed.
Lemma lem3384044 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3384045 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term273 A B s _35496 f _35497) = (term277 A B s f _35496 _35497).
Proof. exact (@lem3384044 (term100 A B s _35496 f _35497) (_35496 = _35497)). Qed.
Lemma lem3384047 (a : Prop) (b : Prop) : (term278 a b) = (term279 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3384048 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term280 A B s _35496 f _35497) = (term281 A B s _35496 f _35497).
Proof. exact (@lem3384047 (term227 A s _35496) (term97 A B s _35496 f _35497)). Qed.
Lemma lem3384050 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384051 {A : Type'} (s : A -> Prop) (_35496 : A) : (term282 A s _35496) = (s _35496).
Proof. exact (@lem3384050 (s _35496)). Qed.
Lemma lem3384052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3384053 {A : Type'} (s : A -> Prop) (_35496 : A) : (term283 A s _35496) = (term27 A s _35496).
Proof. exact (MK_COMB (@lem3384052) (@lem3384051 A s _35496)). Qed.
Lemma lem3384055 (a : Prop) (b : Prop) : (term278 a b) = (term279 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3384056 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term284 A B s _35496 f _35497) = (term285 A B s _35496 f _35497).
Proof. exact (@lem3384055 (term227 A s _35497) (term230 A B _35496 f _35497)). Qed.
Lemma lem3384058 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384059 {A : Type'} (s : A -> Prop) (_35497 : A) : (term282 A s _35497) = (s _35497).
Proof. exact (@lem3384058 (s _35497)). Qed.
Lemma lem3384060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3384061 {A : Type'} (s : A -> Prop) (_35497 : A) : (term283 A s _35497) = (term27 A s _35497).
Proof. exact (MK_COMB (@lem3384060) (@lem3384059 A s _35497)). Qed.
Lemma lem3384063 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384064 {A B : Type'} (_35496 : A) (f : A -> B) (_35497 : A) : (term286 A B _35496 f _35497) = ((f _35496) = (f _35497)).
Proof. exact (@lem3384063 ((f _35496) = (f _35497))). Qed.
Lemma lem3384065 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term285 A B s _35496 f _35497) = (term29 A B s _35496 f _35497).
Proof. exact (MK_COMB (@lem3384061 A s _35497) (@lem3384064 A B _35496 f _35497)). Qed.
Lemma lem3384066 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term284 A B s _35496 f _35497) = (term29 A B s _35496 f _35497).
Proof. exact (TRANS (@lem3384056 A B s _35496 f _35497) (@lem3384065 A B s _35496 f _35497)). Qed.
Lemma lem3384067 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term281 A B s _35496 f _35497) = (term31 A B s _35496 f _35497).
Proof. exact (MK_COMB (@lem3384053 A s _35496) (@lem3384066 A B s _35496 f _35497)). Qed.
Lemma lem3384068 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term280 A B s _35496 f _35497) = (term31 A B s _35496 f _35497).
Proof. exact (TRANS (@lem3384048 A B s _35496 f _35497) (@lem3384067 A B s _35496 f _35497)). Qed.
Lemma lem3384069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3384070 {A B : Type'} (s : A -> Prop) (_35496 : A) (f : A -> B) (_35497 : A) : (term287 A B s _35496 f _35497) = (term33 A B s _35496 f _35497).
Proof. exact (MK_COMB (@lem3384069) (@lem3384068 A B s _35496 f _35497)). Qed.
Lemma lem3384071 {A : Type'} (_35496 : A) (_35497 : A) : (_35496 = _35497) = (_35496 = _35497).
Proof. exact (eq_refl (_35496 = _35497)). Qed.
Lemma lem3384072 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term277 A B s f _35496 _35497) = (term35 A B s f _35496 _35497).
Proof. exact (MK_COMB (@lem3384070 A B s _35496 f _35497) (@lem3384071 A _35496 _35497)). Qed.
Lemma lem3384073 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35496 : A) (_35497 : A) : (term273 A B s _35496 f _35497) = (term35 A B s f _35496 _35497).
Proof. exact (TRANS (@lem3384045 A B s f _35496 _35497) (@lem3384072 A B s f _35496 _35497)). Qed.
Lemma lem3384075 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) (h2 : x = (f a)) : term29 A B s a f x'.
Proof. exact (conj (@lem3383894 A B x' s x f a h1) (@lem3383901 A B x' s x f a h1 h2)). Qed.
Lemma lem3384076 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : term31 A B s a f x'.
Proof. exact (conj (@lem3383887 A B f s a h1) (@lem3384075 A B x' s x f a h2 h3)). Qed.
Lemma lem3384078 {A B : Type'} (_35496 : A) (_35497 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term35 A B s f _35496 _35497.
Proof. exact (EQ_MP (@lem3384073 A B s f _35496 _35497) (@lem3384042 A B _35496 _35497 f s a h1)). Qed.
Lemma lem3384079 {A B : Type'} (_35496 : A) (_35497 : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term35 A B s f _35496 _35497.
Proof. exact (@lem3384078 A B _35496 _35497 f s a h1). Qed.
Lemma lem3384080 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term35 A B s f a x'.
Proof. exact (@lem3384079 A B a x' f s a h1). Qed.
Lemma lem3384083 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : a = x'.
Proof. exact (@lem3384080 A B x' f s a h1 (@lem3384076 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3384084 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : term288 A a x'.
Proof. exact (fun h0 : term55 A a x' => @lem3384083 A B x' s x f a h1 h2 h3). Qed.
Lemma lem3384086 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384087 {A : Type'} (a : A) (x' : A) : (term288 A a x') = (a = x').
Proof. exact (@lem3384086 (a = x')). Qed.
Lemma lem3384088 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : a = x'.
Proof. exact (EQ_MP (@lem3384087 A a x') (@lem3384084 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3384090 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3384091 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3384090 A x). Qed.
Lemma lem3384092 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3384091 A a). Qed.
Lemma lem3384093 {A : Type'} (a : A) : term289 A a.
Proof. exact (fun h0 : term290 A a => @lem3384092 A a). Qed.
Lemma lem3384095 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384096 {A : Type'} (a : A) : (term289 A a) = (a = a).
Proof. exact (@lem3384095 (a = a)). Qed.
Lemma lem3384097 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3384096 A a) (@lem3384093 A a)). Qed.
Lemma lem3384115 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3384116 {A : Type'} (y : A) (x : A) (z : A) : (term291 A x y z) = (term292 A y x z).
Proof. exact (@lem3384115 (y = z) (term55 A x z)). Qed.
Lemma lem3384126 {A : Type'} (x : A) (y : A) : (term293 A x y) = (term293 A x y).
Proof. exact (eq_refl (term293 A x y)). Qed.
Lemma lem3384127 {A : Type'} (y : A) (x : A) (z : A) : (term266 A x y z) = (term294 A y x z).
Proof. exact (MK_COMB (@lem3384126 A x y) (@lem3384116 A y x z)). Qed.
Lemma lem3384131 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3384132 {A : Type'} (y : A) (x : A) (z : A) : (term294 A y x z) = (term295 A y x z).
Proof. exact (@lem3384131 (y = z) (term55 A x y) (term55 A x z)). Qed.
Lemma lem3384154 {A : Type'} (y : A) (x : A) (z : A) : (term266 A x y z) = (term295 A y x z).
Proof. exact (TRANS (@lem3384127 A y x z) (@lem3384132 A y x z)). Qed.
Lemma lem3384155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384156 {A : Type'} (y : A) (x : A) (z : A) : (term296 A x y z) = (term297 A y x z).
Proof. exact (MK_COMB (@lem3384155) (@lem3384154 A y x z)). Qed.
Lemma lem3384178 {A : Type'} (y : A) (x : A) (z : A) : (term295 A y x z) = (term295 A y x z).
Proof. exact (eq_refl (term295 A y x z)). Qed.
Lemma lem3384179 {A : Type'} (y : A) (x : A) (z : A) : ((term266 A x y z) = (term295 A y x z)) = ((term295 A y x z) = (term295 A y x z)).
Proof. exact (MK_COMB (@lem3384156 A y x z) (@lem3384178 A y x z)). Qed.
Lemma lem3384181 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3384182 (x : Prop) : (x = x) = True.
Proof. exact (@lem3384181 Prop x). Qed.
Lemma lem3384183 {A : Type'} (y : A) (x : A) (z : A) : ((term295 A y x z) = (term295 A y x z)) = True.
Proof. exact (@lem3384182 (term295 A y x z)). Qed.
Lemma lem3384184 {A : Type'} (y : A) (x : A) (z : A) : ((term266 A x y z) = (term295 A y x z)) = True.
Proof. exact (TRANS (@lem3384179 A y x z) (@lem3384183 A y x z)). Qed.
Lemma lem3384185 {A : Type'} (y : A) (x : A) (z : A) : True = ((term266 A x y z) = (term295 A y x z)).
Proof. exact (SYM (@lem3384184 A y x z)). Qed.
Lemma lem3384186 {A : Type'} (y : A) (x : A) (z : A) : (term266 A x y z) = (term295 A y x z).
Proof. exact (EQ_MP (@lem3384185 A y x z) (@lem0)). Qed.
Lemma lem3384187 {A : Type'} (y : A) (x : A) (z : A) : term295 A y x z.
Proof. exact (EQ_MP (@lem3384186 A y x z) (@lem3383880 A x y z)). Qed.
Lemma lem3384189 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3384190 {A : Type'} (x : A) (y : A) (z : A) : (term295 A y x z) = (term298 A x y z).
Proof. exact (@lem3384189 (term299 A y x z) (y = z)). Qed.
Lemma lem3384192 (a : Prop) (b : Prop) : (term278 a b) = (term279 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3384193 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term301 A y x z).
Proof. exact (@lem3384192 (term55 A x y) (term55 A x z)). Qed.
Lemma lem3384195 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384196 {A : Type'} (x : A) (y : A) : (term112 A x y) = (x = y).
Proof. exact (@lem3384195 (x = y)). Qed.
Lemma lem3384197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3384198 {A : Type'} (x : A) (y : A) : (term302 A x y) = (term303 A x y).
Proof. exact (MK_COMB (@lem3384197) (@lem3384196 A x y)). Qed.
Lemma lem3384200 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384201 {A : Type'} (x : A) (z : A) : (term112 A x z) = (x = z).
Proof. exact (@lem3384200 (x = z)). Qed.
Lemma lem3384202 {A : Type'} (y : A) (x : A) (z : A) : (term301 A y x z) = (term304 A y x z).
Proof. exact (MK_COMB (@lem3384198 A x y) (@lem3384201 A x z)). Qed.
Lemma lem3384203 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term304 A y x z).
Proof. exact (TRANS (@lem3384193 A y x z) (@lem3384202 A y x z)). Qed.
Lemma lem3384204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3384205 {A : Type'} (y : A) (x : A) (z : A) : (term305 A y x z) = (term306 A y x z).
Proof. exact (MK_COMB (@lem3384204) (@lem3384203 A y x z)). Qed.
Lemma lem3384206 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3384207 {A : Type'} (x : A) (y : A) (z : A) : (term298 A x y z) = (term307 A x y z).
Proof. exact (MK_COMB (@lem3384205 A y x z) (@lem3384206 A y z)). Qed.
Lemma lem3384208 {A : Type'} (x : A) (y : A) (z : A) : (term295 A y x z) = (term307 A x y z).
Proof. exact (TRANS (@lem3384190 A x y z) (@lem3384207 A x y z)). Qed.
Lemma lem3384210 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : term308 A x' a.
Proof. exact (conj (@lem3384088 A B x' s x f a h1 h2 h3) (@lem3384097 A a)). Qed.
Lemma lem3384212 {A : Type'} (x : A) (y : A) (z : A) : term307 A x y z.
Proof. exact (EQ_MP (@lem3384208 A x y z) (@lem3384187 A y x z)). Qed.
Lemma lem3384213 {A : Type'} (x : A) (y : A) (z : A) : term307 A x y z.
Proof. exact (@lem3384212 A x y z). Qed.
Lemma lem3384214 {A : Type'} (x' : A) (a : A) : term309 A x' a.
Proof. exact (@lem3384213 A a x' a). Qed.
Lemma lem3384217 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : x' = a.
Proof. exact (@lem3384214 A x' a (@lem3384210 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3384218 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : term288 A x' a.
Proof. exact (fun h0 : term55 A x' a => @lem3384217 A B x' s x f a h1 h2 h3). Qed.
Lemma lem3384220 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384221 {A : Type'} (x' : A) (a : A) : (term288 A x' a) = (x' = a).
Proof. exact (@lem3384220 (x' = a)). Qed.
Lemma lem3384222 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : x' = a.
Proof. exact (EQ_MP (@lem3384221 A x' a) (@lem3384218 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3384225 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3384227 {A : Type'} (x' : A) (a : A) : (term55 A x' a) = (term310 A x' a).
Proof. exact (@lem3384225 (x' = a)). Qed.
Lemma lem3384230 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term167 A B x' s x f a) : term310 A x' a.
Proof. exact (EQ_MP (@lem3384227 A x' a) (@lem3383713 A B x' s x f a h1)). Qed.
Lemma lem3384233 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (@lem3384230 A B x' s x f a h2 (@lem3384222 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3384234 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : term265.
Proof. exact (fun h0 : ~ False => @lem3384233 A B x' s x f a h1 h2 h3). Qed.
Lemma lem3384236 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384237 : term265 = False.
Proof. exact (@lem3384236 False). Qed.
Lemma lem3384251 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3384252 {A : Type'} (_35547 : A) (_35548 : A) (h1 : _35547 = _35548) : _35547 = _35548.
Proof. exact (h1). Qed.
Lemma lem3384253 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) (h1 : _35547 = _35548) : (f _35547) = (f _35548).
Proof. exact (MK_COMB (@lem3384251 A B f) (@lem3384252 A _35547 _35548 h1)). Qed.
Lemma lem3384254 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : term311 A B _35547 f _35548.
Proof. exact (fun h0 : _35547 = _35548 => @lem3384253 A B f _35547 _35548 h0). Qed.
Lemma lem3384256 (a : Prop) (b : Prop) : (a -> b) = (term312 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3384257 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : (term311 A B _35547 f _35548) = (term313 A B _35547 f _35548).
Proof. exact (@lem3384256 (_35547 = _35548) ((f _35547) = (f _35548))). Qed.
Lemma lem3384258 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : term313 A B _35547 f _35548.
Proof. exact (EQ_MP (@lem3384257 A B _35547 f _35548) (@lem3384254 A B _35547 f _35548)). Qed.
Lemma lem3384264 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3384265 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3384264 B x). Qed.
Lemma lem3384266 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3384265 B (f x')). Qed.
Lemma lem3384267 {A B : Type'} (f : A -> B) (x' : A) : term254 A B f x'.
Proof. exact (fun h0 : term255 A B f x' => @lem3384266 A B f x'). Qed.
Lemma lem3384269 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384270 {A B : Type'} (f : A -> B) (x' : A) : (term254 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3384269 ((f x') = (f x'))). Qed.
Lemma lem3384271 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3384270 A B f x') (@lem3384267 A B f x')). Qed.
Lemma lem3384273 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : s x'.
Proof. exact (proj2 (@lem3383257 A B s x' x f a h1)). Qed.
Lemma lem3384274 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term257 A s x'.
Proof. exact (fun h0 : term227 A s x' => @lem3384273 A B s x' x f a h1). Qed.
Lemma lem3384276 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384277 {A : Type'} (s : A -> Prop) (x' : A) : (term257 A s x') = (s x').
Proof. exact (@lem3384276 (s x')). Qed.
Lemma lem3384278 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : s x'.
Proof. exact (EQ_MP (@lem3384277 A s x') (@lem3384274 A B s x' x f a h1)). Qed.
Lemma lem3384284 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3384285 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) (a : A) : (term246 A B x' f s _35500 a) = (term314 A B s x' f _35500 a).
Proof. exact (@lem3384284 (term227 A s _35500) (term230 A B x' f _35500) (_35500 = a)). Qed.
Lemma lem3384299 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3384300 {A B : Type'} (a : A) (x' : A) (f : A -> B) (_35500 : A) : (term315 A B x' f _35500 a) = (term316 A B a x' f _35500).
Proof. exact (@lem3384299 (_35500 = a) (term230 A B x' f _35500)). Qed.
Lemma lem3384310 {A : Type'} (s : A -> Prop) (_35500 : A) : (term98 A s _35500) = (term98 A s _35500).
Proof. exact (eq_refl (term98 A s _35500)). Qed.
Lemma lem3384311 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (_35500 : A) : (term314 A B s x' f _35500 a) = (term317 A B s a x' f _35500).
Proof. exact (MK_COMB (@lem3384310 A s _35500) (@lem3384300 A B a x' f _35500)). Qed.
Lemma lem3384315 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3384316 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : (term317 A B s a x' f _35500) = (term318 A B a s x' f _35500).
Proof. exact (@lem3384315 (_35500 = a) (term227 A s _35500) (term230 A B x' f _35500)). Qed.
Lemma lem3384336 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : (term314 A B s x' f _35500 a) = (term318 A B a s x' f _35500).
Proof. exact (TRANS (@lem3384311 A B s a x' f _35500) (@lem3384316 A B a s x' f _35500)). Qed.
Lemma lem3384337 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : (term246 A B x' f s _35500 a) = (term318 A B a s x' f _35500).
Proof. exact (TRANS (@lem3384285 A B s x' f _35500 a) (@lem3384336 A B a s x' f _35500)). Qed.
Lemma lem3384338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384339 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : (term319 A B x' f s _35500 a) = (term320 A B a s x' f _35500).
Proof. exact (MK_COMB (@lem3384338) (@lem3384337 A B a s x' f _35500)). Qed.
Lemma lem3384355 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3384356 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : (term235 A B x' f s _35500) = (term97 A B s x' f _35500).
Proof. exact (@lem3384355 (term227 A s _35500) (term230 A B x' f _35500)). Qed.
Lemma lem3384364 {A : Type'} (_35500 : A) (a : A) : (term321 A _35500 a) = (term321 A _35500 a).
Proof. exact (eq_refl (term321 A _35500 a)). Qed.
Lemma lem3384365 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : (term322 A B a x' f s _35500) = (term318 A B a s x' f _35500).
Proof. exact (MK_COMB (@lem3384364 A _35500 a) (@lem3384356 A B s x' f _35500)). Qed.
Lemma lem3384376 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : ((term246 A B x' f s _35500 a) = (term322 A B a x' f s _35500)) = ((term318 A B a s x' f _35500) = (term318 A B a s x' f _35500)).
Proof. exact (MK_COMB (@lem3384339 A B a s x' f _35500) (@lem3384365 A B a s x' f _35500)). Qed.
Lemma lem3384378 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3384379 (x : Prop) : (x = x) = True.
Proof. exact (@lem3384378 Prop x). Qed.
Lemma lem3384380 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35500 : A) : ((term318 A B a s x' f _35500) = (term318 A B a s x' f _35500)) = True.
Proof. exact (@lem3384379 (term318 A B a s x' f _35500)). Qed.
Lemma lem3384381 {A B : Type'} (a : A) (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : ((term246 A B x' f s _35500 a) = (term322 A B a x' f s _35500)) = True.
Proof. exact (TRANS (@lem3384376 A B a s x' f _35500) (@lem3384380 A B a s x' f _35500)). Qed.
Lemma lem3384382 {A B : Type'} (a : A) (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : True = ((term246 A B x' f s _35500 a) = (term322 A B a x' f s _35500)).
Proof. exact (SYM (@lem3384381 A B a x' f s _35500)). Qed.
Lemma lem3384383 {A B : Type'} (a : A) (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : (term246 A B x' f s _35500 a) = (term322 A B a x' f s _35500).
Proof. exact (EQ_MP (@lem3384382 A B a x' f s _35500) (@lem0)). Qed.
Lemma lem3384384 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term322 A B a x' f s _35500.
Proof. exact (EQ_MP (@lem3384383 A B a x' f s _35500) (@lem3383768 A B _35500 s x' x f a h1)). Qed.
Lemma lem3384386 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3384387 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term322 A B a x' f s _35500) = (term323 A B x' f s _35500 a).
Proof. exact (@lem3384386 (term235 A B x' f s _35500) (_35500 = a)). Qed.
Lemma lem3384389 (a : Prop) (b : Prop) : (term278 a b) = (term279 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3384390 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : (term324 A B x' f s _35500) = (term325 A B x' f s _35500).
Proof. exact (@lem3384389 (term230 A B x' f _35500) (term227 A s _35500)). Qed.
Lemma lem3384392 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384393 {A B : Type'} (x' : A) (f : A -> B) (_35500 : A) : (term286 A B x' f _35500) = ((f x') = (f _35500)).
Proof. exact (@lem3384392 ((f x') = (f _35500))). Qed.
Lemma lem3384394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3384395 {A B : Type'} (x' : A) (f : A -> B) (_35500 : A) : (term326 A B x' f _35500) = (term327 A B x' f _35500).
Proof. exact (MK_COMB (@lem3384394) (@lem3384393 A B x' f _35500)). Qed.
Lemma lem3384397 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384398 {A : Type'} (s : A -> Prop) (_35500 : A) : (term282 A s _35500) = (s _35500).
Proof. exact (@lem3384397 (s _35500)). Qed.
Lemma lem3384399 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : (term325 A B x' f s _35500) = (term262 A B x' f s _35500).
Proof. exact (MK_COMB (@lem3384395 A B x' f _35500) (@lem3384398 A s _35500)). Qed.
Lemma lem3384400 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : (term324 A B x' f s _35500) = (term262 A B x' f s _35500).
Proof. exact (TRANS (@lem3384390 A B x' f s _35500) (@lem3384399 A B x' f s _35500)). Qed.
Lemma lem3384401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3384402 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) : (term328 A B x' f s _35500) = (term329 A B x' f s _35500).
Proof. exact (MK_COMB (@lem3384401) (@lem3384400 A B x' f s _35500)). Qed.
Lemma lem3384403 {A : Type'} (_35500 : A) (a : A) : (_35500 = a) = (_35500 = a).
Proof. exact (eq_refl (_35500 = a)). Qed.
Lemma lem3384404 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term323 A B x' f s _35500 a) = (term330 A B x' f s _35500 a).
Proof. exact (MK_COMB (@lem3384402 A B x' f s _35500) (@lem3384403 A _35500 a)). Qed.
Lemma lem3384405 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35500 : A) (a : A) : (term322 A B a x' f s _35500) = (term330 A B x' f s _35500 a).
Proof. exact (TRANS (@lem3384387 A B x' f s _35500 a) (@lem3384404 A B x' f s _35500 a)). Qed.
Lemma lem3384407 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term263 A B f s x'.
Proof. exact (conj (@lem3384271 A B f x') (@lem3384278 A B s x' x f a h1)). Qed.
Lemma lem3384409 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term330 A B x' f s _35500 a.
Proof. exact (EQ_MP (@lem3384405 A B x' f s _35500 a) (@lem3384384 A B _35500 s x' x f a h1)). Qed.
Lemma lem3384410 {A B : Type'} (_35500 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term330 A B x' f s _35500 a.
Proof. exact (@lem3384409 A B _35500 s x' x f a h1). Qed.
Lemma lem3384411 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term331 A B f s x' a.
Proof. exact (@lem3384410 A B x' s x' x f a h1). Qed.
Lemma lem3384414 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : x' = a.
Proof. exact (@lem3384411 A B s x' x f a h1 (@lem3384407 A B s x' x f a h1)). Qed.
Lemma lem3384415 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term288 A x' a.
Proof. exact (fun h0 : term55 A x' a => @lem3384414 A B s x' x f a h1). Qed.
Lemma lem3384417 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384418 {A : Type'} (x' : A) (a : A) : (term288 A x' a) = (x' = a).
Proof. exact (@lem3384417 (x' = a)). Qed.
Lemma lem3384419 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : x' = a.
Proof. exact (EQ_MP (@lem3384418 A x' a) (@lem3384415 A B s x' x f a h1)). Qed.
Lemma lem3384425 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3384426 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : (term313 A B _35547 f _35548) = (term332 A B f _35547 _35548).
Proof. exact (@lem3384425 ((f _35547) = (f _35548)) (term55 A _35547 _35548)). Qed.
Lemma lem3384436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384437 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : (term333 A B _35547 f _35548) = (term334 A B f _35547 _35548).
Proof. exact (MK_COMB (@lem3384436) (@lem3384426 A B f _35547 _35548)). Qed.
Lemma lem3384447 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : (term332 A B f _35547 _35548) = (term332 A B f _35547 _35548).
Proof. exact (eq_refl (term332 A B f _35547 _35548)). Qed.
Lemma lem3384448 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : ((term313 A B _35547 f _35548) = (term332 A B f _35547 _35548)) = ((term332 A B f _35547 _35548) = (term332 A B f _35547 _35548)).
Proof. exact (MK_COMB (@lem3384437 A B f _35547 _35548) (@lem3384447 A B f _35547 _35548)). Qed.
Lemma lem3384450 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3384451 (x : Prop) : (x = x) = True.
Proof. exact (@lem3384450 Prop x). Qed.
Lemma lem3384452 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : ((term332 A B f _35547 _35548) = (term332 A B f _35547 _35548)) = True.
Proof. exact (@lem3384451 (term332 A B f _35547 _35548)). Qed.
Lemma lem3384453 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : ((term313 A B _35547 f _35548) = (term332 A B f _35547 _35548)) = True.
Proof. exact (TRANS (@lem3384448 A B f _35547 _35548) (@lem3384452 A B f _35547 _35548)). Qed.
Lemma lem3384454 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : True = ((term313 A B _35547 f _35548) = (term332 A B f _35547 _35548)).
Proof. exact (SYM (@lem3384453 A B f _35547 _35548)). Qed.
Lemma lem3384455 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : (term313 A B _35547 f _35548) = (term332 A B f _35547 _35548).
Proof. exact (EQ_MP (@lem3384454 A B f _35547 _35548) (@lem0)). Qed.
Lemma lem3384456 {A B : Type'} (f : A -> B) (_35547 : A) (_35548 : A) : term332 A B f _35547 _35548.
Proof. exact (EQ_MP (@lem3384455 A B f _35547 _35548) (@lem3384258 A B _35547 f _35548)). Qed.
Lemma lem3384458 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3384459 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : (term332 A B f _35547 _35548) = (term335 A B _35547 f _35548).
Proof. exact (@lem3384458 (term55 A _35547 _35548) ((f _35547) = (f _35548))). Qed.
Lemma lem3384461 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3384462 {A : Type'} (_35547 : A) (_35548 : A) : (term112 A _35547 _35548) = (_35547 = _35548).
Proof. exact (@lem3384461 (_35547 = _35548)). Qed.
Lemma lem3384463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3384464 {A : Type'} (_35547 : A) (_35548 : A) : (term336 A _35547 _35548) = (term337 A _35547 _35548).
Proof. exact (MK_COMB (@lem3384463) (@lem3384462 A _35547 _35548)). Qed.
Lemma lem3384465 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : ((f _35547) = (f _35548)) = ((f _35547) = (f _35548)).
Proof. exact (eq_refl ((f _35547) = (f _35548))). Qed.
Lemma lem3384466 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : (term335 A B _35547 f _35548) = (term311 A B _35547 f _35548).
Proof. exact (MK_COMB (@lem3384464 A _35547 _35548) (@lem3384465 A B _35547 f _35548)). Qed.
Lemma lem3384467 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : (term332 A B f _35547 _35548) = (term311 A B _35547 f _35548).
Proof. exact (TRANS (@lem3384459 A B _35547 f _35548) (@lem3384466 A B _35547 f _35548)). Qed.
Lemma lem3384470 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : term311 A B _35547 f _35548.
Proof. exact (EQ_MP (@lem3384467 A B _35547 f _35548) (@lem3384456 A B f _35547 _35548)). Qed.
Lemma lem3384471 {A B : Type'} (_35547 : A) (f : A -> B) (_35548 : A) : term311 A B _35547 f _35548.
Proof. exact (@lem3384470 A B _35547 f _35548). Qed.
Lemma lem3384472 {A B : Type'} (x' : A) (f : A -> B) (a : A) : term311 A B x' f a.
Proof. exact (@lem3384471 A B x' f a). Qed.
Lemma lem3384475 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : (f x') = (f a).
Proof. exact (@lem3384472 A B x' f a (@lem3384419 A B s x' x f a h1)). Qed.
Lemma lem3384476 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term267 A B x' f a.
Proof. exact (fun h0 : term230 A B x' f a => @lem3384475 A B s x' x f a h1). Qed.
Lemma lem3384478 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384479 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term267 A B x' f a) = ((f x') = (f a)).
Proof. exact (@lem3384478 ((f x') = (f a))). Qed.
Lemma lem3384480 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : (f x') = (f a).
Proof. exact (EQ_MP (@lem3384479 A B x' f a) (@lem3384476 A B s x' x f a h1)). Qed.
Lemma lem3384483 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3384485 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term230 A B x' f a) = (term338 A B x' f a).
Proof. exact (@lem3384483 ((f x') = (f a))). Qed.
Lemma lem3384488 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term338 A B x' f a.
Proof. exact (EQ_MP (@lem3384485 A B x' f a) (@lem3383781 A B s x' x f a h1)). Qed.
Lemma lem3384491 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : False.
Proof. exact (@lem3384488 A B s x' x f a h1 (@lem3384480 A B s x' x f a h1)). Qed.
Lemma lem3384492 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : term265.
Proof. exact (fun h0 : ~ False => @lem3384491 A B s x' x f a h1). Qed.
Lemma lem3384494 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3384495 : term265 = False.
Proof. exact (@lem3384494 False). Qed.
Lemma lem3384497 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term197 A B s x' x f a) : False.
Proof. exact (EQ_MP (@lem3384495) (@lem3384492 A B s x' x f a h1)). Qed.
Lemma lem3384498 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3384237) (@lem3384234 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3384499 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : False.
Proof. exact (EQ_MP (@lem3383855) (@lem3383852 A B x' s x f a h1 h2)). Qed.
Lemma lem3384500 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : (x = (f a)) = False.
Proof. exact (prop_ext (fun h4 : x = (f a) => @lem3384498 A B x' s x f a h1 h2 h3) (fun h4 : False => @lem3383511 A B x f a h3)). Qed.
Lemma lem3384501 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3384500 A B x' s x f a h1 h2 h3) (@lem3383511 A B x f a h3)). Qed.
Lemma lem3384502 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : (x = (f a)) = False.
Proof. exact (prop_ext (fun h4 : x = (f a) => @lem3384501 A B x' s x f a h1 h2 h3) (fun h4 : False => @lem3383364 A B x f a h3)). Qed.
Lemma lem3384503 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3384502 A B x' s x f a h1 h2 h3) (@lem3383364 A B x f a h3)). Qed.
Lemma lem3384504 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : (x = (f a)) = False.
Proof. exact (prop_ext (fun h4 : x = (f a) => @lem3384503 A B x' s x f a h1 h2 h3) (fun h4 : False => @lem3383364 A B x f a h3)). Qed.
Lemma lem3384505 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3384504 A B x' s x f a h1 h2 h3) (@lem3383364 A B x f a h3)). Qed.
Lemma lem3384506 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : (term137 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term137 A B x f s => @lem3384499 A B x' s x f a h1 h2) (fun h3 : False => @lem3383316 A B x f s h1)). Qed.
Lemma lem3384507 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term137 A B x f s) (h2 : term167 A B x' s x f a) : False.
Proof. exact (EQ_MP (@lem3384506 A B x' s x f a h1 h2) (@lem3383316 A B x f s h1)). Qed.
Lemma lem3384508 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term167 A B x' s x f a) : False.
Proof. exact (or_elim (@lem3383246 A B x' s x f a h2) (fun h0 : term137 A B x f s => @lem3384507 A B x' s x f a h0 h2) (fun h0 : x = (f a) => @lem3384505 A B x' s x f a h1 h2 h0)). Qed.
Lemma lem3384509 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term218 A B s x' x f a) : False.
Proof. exact (or_elim (@lem3383241 A B s x' x f a h2) (fun h0 : term167 A B x' s x f a => @lem3384508 A B x' s x f a h1 h0) (fun h0 : term197 A B s x' x f a => @lem3384497 A B s x' x f a h0)). Qed.
Lemma lem3384510 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term218 A B s x' x f a) : (term218 A B s x' x f a) = False.
Proof. exact (prop_ext (fun h3 : term218 A B s x' x f a => @lem3384509 A B s x' x f a h1 h2) (fun h3 : False => @lem3383241 A B s x' x f a h2)). Qed.
Lemma lem3384511 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term47 A B f s a) (h2 : term218 A B s x' x f a) : False.
Proof. exact (EQ_MP (@lem3384510 A B s x' x f a h1 h2) (@lem3383241 A B s x' x f a h2)). Qed.
Lemma lem3384512 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term95 A B s x f a) (h2 : term47 A B f s a) : False.
Proof. exact (ex_elim (@lem3383076 A B s x f a h1) (fun x' : A => fun h0 : term220 A B s x f a x' => @lem3384511 A B s x' x f a h2 h0)). Qed.
Lemma lem3384513 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term95 A B s x f a) (h2 : term47 A B f s a) : (term95 A B s x f a) = False.
Proof. exact (prop_ext (fun h3 : term95 A B s x f a => @lem3384512 A B x f s a h1 h2) (fun h3 : False => @lem3382623 A B s x f a h1)). Qed.
Lemma lem3384514 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term95 A B s x f a) (h2 : term47 A B f s a) : False.
Proof. exact (EQ_MP (@lem3384513 A B x f s a h1 h2) (@lem3382623 A B s x f a h1)). Qed.
Lemma lem3384515 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term94 A B s x f a.
Proof. exact (fun h0 : term95 A B s x f a => @lem3384514 A B x f s a h0 h1). Qed.
Lemma lem3384516 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : (term62 A B x f s a) = (term75 A B s x f a).
Proof. exact (EQ_MP (@lem3382622 A B s x f a) (@lem3384515 A B x f s a h1)). Qed.
Lemma lem3384521 {A B : Type'} (f : A -> B) (s : A -> Prop) (a : A) (h1 : term47 A B f s a) : term78 A B s f a.
Proof. exact (fun x : B => @lem3384516 A B x f s a h1). Qed.
Lemma lem3384522 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : term79 A B s f a.
Proof. exact (fun h0 : term47 A B f s a => @lem3384521 A B f s a h0). Qed.
Lemma lem3384527 {A B : Type'} (s : A -> Prop) (f : A -> B) : term81 A B s f.
Proof. exact (fun a : A => @lem3384522 A B s f a). Qed.
Lemma lem3384532 {A B : Type'} (f : A -> B) : term83 A B f.
Proof. exact (fun s : A -> Prop => @lem3384527 A B s f). Qed.
Lemma lem3384537 {A B : Type'} : term85 A B.
Proof. exact (fun f : A -> B => @lem3384532 A B f). Qed.
Lemma lem3384538 {A B : Type'} : term87 A B.
Proof. exact (EQ_MP (@lem3382617 A B) (@lem3384537 A B)). Qed.
Lemma lem3384540 {A B : Type'} : term87 A B.
Proof. exact (@lem3382345 A B (@lem3384538 A B)). Qed.
Lemma lem3384541 {A B : Type'} (h1 : term88 A B) : False.
Proof. exact (@lem3384540 A B (@lem3382329 A B h1)). Qed.
Lemma lem3384542 {A B : Type'} (h1 : term88 A B) : (term88 A B) = False.
Proof. exact (prop_ext (fun h2 : term88 A B => @lem3384541 A B h1) (fun h2 : False => @lem3382329 A B h1)). Qed.
Lemma lem3384543 {A B : Type'} (h1 : term88 A B) : False.
Proof. exact (EQ_MP (@lem3384542 A B h1) (@lem3382329 A B h1)). Qed.
Lemma lem3384544 {A B : Type'} : term87 A B.
Proof. exact (fun h0 : term88 A B => @lem3384543 A B h0). Qed.
Lemma lem3384545 {A B : Type'} : term85 A B.
Proof. exact (EQ_MP (@lem3382328 A B) (@lem3384544 A B)). Qed.
Lemma lem3384546 {A B : Type'} : term25 A B.
Proof. exact (EQ_MP (@lem3382324 A B) (@lem3384545 A B)). Qed.
Lemma lem3384547 {A B : Type'} : term24 A B.
Proof. exact (EQ_MP (@lem3382111 A B) (@lem3384546 A B)). Qed.
