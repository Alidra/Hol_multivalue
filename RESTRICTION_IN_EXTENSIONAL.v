Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_IN_EXTENSIONAL_term_abbrevs.
Require Import IN_EXTENSIONAL_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem4387093 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4387094 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4387095 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4387094 A B s) (@lem4387093 A B s)). Qed.
Lemma lem4387096 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4387095 A B s f). Qed.
Lemma lem4387097 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4387098 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4387097 A B s f) (@lem4387096 A B s f)). Qed.
Lemma lem4387099 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4387098 A B s f x). Qed.
Lemma lem4387100 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4387102 {A B : Type'} (s : A -> Prop) : term6 A B s.
Proof. exact (@lem4382932 A B s). Qed.
Lemma lem4387103 {A B : Type'} (s : A -> Prop) : (term6 A B s) = (term7 A B s).
Proof. exact (eq_refl (term6 A B s)). Qed.
Lemma lem4387104 {A B : Type'} (s : A -> Prop) : term7 A B s.
Proof. exact (EQ_MP (@lem4387103 A B s) (@lem4387102 A B s)). Qed.
Lemma lem4387105 {A B : Type'} (s : A -> Prop) (f : A -> B) : term8 A B s f.
Proof. exact (@lem4387104 A B s f). Qed.
Lemma lem4387106 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term8 A B s f) = ((term9 A B f s) = (term10 A B s f)).
Proof. exact (eq_refl (term8 A B s f)). Qed.
Lemma lem4387117 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term9 A B f s) = (term10 A B s f).
Proof. exact (EQ_MP (@lem4387106 A B s f) (@lem4387105 A B s f)). Qed.
Lemma lem4387118 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term9 A B f s) = (term10 A B s f).
Proof. exact (@lem4387117 A B s f). Qed.
Lemma lem4387119 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B f s) = (term12 A B s f).
Proof. exact (@lem4387118 A B s (@RESTRICTION A B s f)). Qed.
Lemma lem4387127 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4387128 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem4387127 p q p' q'). Qed.
Lemma lem4387129 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem4387128 p q p'). Qed.
Lemma lem4387130 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term16 A B s f x.
Proof. exact (@lem4387129 (term17 A x s) ((@RESTRICTION A B s f x) = (@ARB B))). Qed.
Lemma lem4387131 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term18 A B s f x p'.
Proof. exact (@lem4387130 A B s f x p'). Qed.
Lemma lem4387132 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term18 A B s f x p') = (term19 A B s f x p').
Proof. exact (eq_refl (term18 A B s f x p')). Qed.
Lemma lem4387133 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term19 A B s f x p'.
Proof. exact (EQ_MP (@lem4387132 A B s f x p') (@lem4387131 A B s f x p')). Qed.
Lemma lem4387134 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term20 A B s f x p' q'.
Proof. exact (@lem4387133 A B s f x p' q'). Qed.
Lemma lem4387135 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term20 A B s f x p' q') = (term21 A B s f x p' q').
Proof. exact (eq_refl (term20 A B s f x p' q')). Qed.
Lemma lem4387136 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term21 A B s f x p' q'.
Proof. exact (EQ_MP (@lem4387135 A B s f x p' q') (@lem4387134 A B s f x p' q')). Qed.
Lemma lem4387137 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (term17 A x s).
Proof. exact (eq_refl (term17 A x s)). Qed.
Lemma lem4387138 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term22 A B f x s q'.
Proof. exact (@lem4387136 A B s f x (term17 A x s) q'). Qed.
Lemma lem4387139 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term23 A B f x s q'.
Proof. exact (@lem4387138 A B f x s q' (@lem4387137 A x s)). Qed.
Lemma lem4387140 {A : Type'} (x : A) (s : A -> Prop) (h1 : term17 A x s) : term17 A x s.
Proof. exact (h1). Qed.
Lemma lem4387141 {A : Type'} (x : A) (s : A -> Prop) : term24 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4387146 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4387100 A B s f x) (@lem4387099 A B s f x)). Qed.
Lemma lem4387147 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4387146 A B s f x). Qed.
Lemma lem4387149 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term25 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4387150 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term26 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4387149 _2963 g t e g' t' e'). Qed.
Lemma lem4387151 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term27 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4387150 _2963 g t e g' t'). Qed.
Lemma lem4387152 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term28 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4387151 _2963 g t e g'). Qed.
Lemma lem4387153 {B : Type'} (g : Prop) (t : B) (e : B) : term28 B g t e.
Proof. exact (@lem4387152 B g t e). Qed.
Lemma lem4387154 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term29 A B s f x.
Proof. exact (@lem4387153 B (@IN A x s) (f x) (@ARB B)). Qed.
Lemma lem4387155 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term30 A B s f x g'.
Proof. exact (@lem4387154 A B s f x g'). Qed.
Lemma lem4387156 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : (term30 A B s f x g') = (term31 A B s f x g').
Proof. exact (eq_refl (term30 A B s f x g')). Qed.
Lemma lem4387157 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term31 A B s f x g'.
Proof. exact (EQ_MP (@lem4387156 A B s f x g') (@lem4387155 A B s f x g')). Qed.
Lemma lem4387158 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term32 A B s f x g' t'.
Proof. exact (@lem4387157 A B s f x g' t'). Qed.
Lemma lem4387159 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : (term32 A B s f x g' t') = (term33 A B s f x g' t').
Proof. exact (eq_refl (term32 A B s f x g' t')). Qed.
Lemma lem4387160 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term33 A B s f x g' t'.
Proof. exact (EQ_MP (@lem4387159 A B s f x g' t') (@lem4387158 A B s f x g' t')). Qed.
Lemma lem4387161 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term34 A B s f x g' t' e'.
Proof. exact (@lem4387160 A B s f x g' t' e'). Qed.
Lemma lem4387162 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : (term34 A B s f x g' t' e') = (term35 A B s f x g' t' e').
Proof. exact (eq_refl (term34 A B s f x g' t' e')). Qed.
Lemma lem4387163 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term35 A B s f x g' t' e'.
Proof. exact (EQ_MP (@lem4387162 A B s f x g' t' e') (@lem4387161 A B s f x g' t' e')). Qed.
Lemma lem4387165 {A : Type'} (x : A) (s : A -> Prop) (h1 : term17 A x s) : (@IN A x s) = False.
Proof. exact (@lem4387141 A x s (@lem4387140 A x s h1)). Qed.
Lemma lem4387166 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B) (e' : B) : term36 A B s f x t' e'.
Proof. exact (@lem4387163 A B s f x False t' e'). Qed.
Lemma lem4387167 {A B : Type'} (f : A -> B) (t' : B) (e' : B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : term37 A B s f x t' e'.
Proof. exact (@lem4387166 A B s f x t' e' (@lem4387165 A x s h1)). Qed.
Lemma lem4387171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4387172 {A B : Type'} (f : A -> B) (x : A) : term38 A B f x.
Proof. exact (fun h0 : False => @lem4387171 A B f x). Qed.
Lemma lem4387173 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : term39 A B s f x e'.
Proof. exact (@lem4387167 A B f (f x) e' x s h1). Qed.
Lemma lem4387174 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : term40 A B s f x e'.
Proof. exact (@lem4387173 A B f e' x s h1 (@lem4387172 A B f x)). Qed.
Lemma lem4387180 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4387181 {B : Type'} : term41 B.
Proof. exact (fun h0 : ~ False => @lem4387180 B). Qed.
Lemma lem4387182 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : term42 A B s f x.
Proof. exact (@lem4387174 A B f (@ARB B) x s h1). Qed.
Lemma lem4387183 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : (term5 A B s f x) = (term43 A B f x).
Proof. exact (@lem4387182 A B f x s h1 (@lem4387181 B)). Qed.
Lemma lem4387185 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4387186 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4387185 B t1 t2). Qed.
Lemma lem4387187 {A B : Type'} (f : A -> B) (x : A) : (term43 A B f x) = (@ARB B).
Proof. exact (@lem4387186 B (f x) (@ARB B)). Qed.
Lemma lem4387188 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : (term5 A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4387183 A B f x s h1) (@lem4387187 A B f x)). Qed.
Lemma lem4387189 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : (@RESTRICTION A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4387147 A B s f x) (@lem4387188 A B f x s h1)). Qed.
Lemma lem4387190 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4387191 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : (term44 A B s f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4387190 B) (@lem4387189 A B f x s h1)). Qed.
Lemma lem4387192 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4387193 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : ((@RESTRICTION A B s f x) = (@ARB B)) = ((@ARB B) = (@ARB B)).
Proof. exact (MK_COMB (@lem4387191 A B f x s h1) (@lem4387192 B)). Qed.
Lemma lem4387195 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4387196 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4387195 B x). Qed.
Lemma lem4387197 {B : Type'} : ((@ARB B) = (@ARB B)) = True.
Proof. exact (@lem4387196 B (@ARB B)). Qed.
Lemma lem4387198 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A x s) : ((@RESTRICTION A B s f x) = (@ARB B)) = True.
Proof. exact (TRANS (@lem4387193 A B f x s h1) (@lem4387197 B)). Qed.
Lemma lem4387199 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term45 A B s f x.
Proof. exact (fun h0 : term17 A x s => @lem4387198 A B f x s h0). Qed.
Lemma lem4387200 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term46 A B f x s.
Proof. exact (@lem4387139 A B f x s True). Qed.
Lemma lem4387201 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term47 A B s f x) = (term48 A x s).
Proof. exact (@lem4387200 A B f x s (@lem4387199 A B s f x)). Qed.
Lemma lem4387203 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4387204 {A : Type'} (x : A) (s : A -> Prop) : (term48 A x s) = True.
Proof. exact (@lem4387203 (term17 A x s)). Qed.
Lemma lem4387205 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term47 A B s f x) = True.
Proof. exact (TRANS (@lem4387201 A B f x s) (@lem4387204 A x s)). Qed.
Lemma lem4387206 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term50 A).
Proof. exact (fun_ext (fun x : A => @lem4387205 A B s f x)). Qed.
Lemma lem4387207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387208 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term12 A B s f) = (term51 A).
Proof. exact (MK_COMB (@lem4387207 A) (@lem4387206 A B s f)). Qed.
Lemma lem4387210 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387211 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem4387210 A t). Qed.
Lemma lem4387212 {A : Type'} : (term51 A) = True.
Proof. exact (@lem4387211 A True). Qed.
Lemma lem4387213 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term12 A B s f) = True.
Proof. exact (TRANS (@lem4387208 A B s f) (@lem4387212 A)). Qed.
Lemma lem4387214 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term11 A B f s) = True.
Proof. exact (TRANS (@lem4387119 A B s f) (@lem4387213 A B s f)). Qed.
Lemma lem4387215 {A B : Type'} (s : A -> Prop) : (term53 A B s) = (term54 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4387214 A B f s)). Qed.
Lemma lem4387216 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4387217 {A B : Type'} (s : A -> Prop) : (term55 A B s) = (term56 A B).
Proof. exact (MK_COMB (@lem4387216 A B) (@lem4387215 A B s)). Qed.
Lemma lem4387219 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387220 {A B : Type'} (t : Prop) : (term57 A B t) = t.
Proof. exact (@lem4387219 (A -> B) t). Qed.
Lemma lem4387221 {A B : Type'} : (term56 A B) = True.
Proof. exact (@lem4387220 A B True). Qed.
Lemma lem4387222 {A B : Type'} (s : A -> Prop) : (term55 A B s) = True.
Proof. exact (TRANS (@lem4387217 A B s) (@lem4387221 A B)). Qed.
Lemma lem4387223 {A B : Type'} : (term58 A B) = (term59 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4387222 A B s)). Qed.
Lemma lem4387224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4387225 {A B : Type'} : (term60 A B) = (term61 A).
Proof. exact (MK_COMB (@lem4387224 A) (@lem4387223 A B)). Qed.
Lemma lem4387227 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4387228 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (@lem4387227 (A -> Prop) t). Qed.
Lemma lem4387229 {A : Type'} : (term61 A) = True.
Proof. exact (@lem4387228 A True). Qed.
Lemma lem4387230 {A B : Type'} : (term60 A B) = True.
Proof. exact (TRANS (@lem4387225 A B) (@lem4387229 A)). Qed.
Lemma lem4387231 {A B : Type'} : True = (term60 A B).
Proof. exact (SYM (@lem4387230 A B)). Qed.
Lemma lem4387232 {A B : Type'} : term60 A B.
Proof. exact (EQ_MP (@lem4387231 A B) (@lem0)). Qed.
