Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXTENSIONAL_EMPTY_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_EXTENSIONAL_spec.
Require Import IN_SING_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem4383143 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4383144 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem4383145 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem4383144 A B f) (@lem4383143 A B f)). Qed.
Lemma lem4383146 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem4383145 A B f g). Qed.
Lemma lem4383147 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem4383149 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4383150 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem4383151 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem4383150 A x) (@lem4383149 A x)). Qed.
Lemma lem4383152 {A : Type'} (x : A) : term6 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4383154 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4383155 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem4383156 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem4383155 A x) (@lem4383154 A x)). Qed.
Lemma lem4383157 {A : Type'} (x : A) (y : A) : term9 A x y.
Proof. exact (@lem4383156 A x y). Qed.
Lemma lem4383158 {A : Type'} (x : A) (y : A) : (term9 A x y) = ((term10 A x y) = (x = y)).
Proof. exact (eq_refl (term9 A x y)). Qed.
Lemma lem4383160 {A B : Type'} (s : A -> Prop) : term11 A B s.
Proof. exact (@lem4382932 A B s). Qed.
Lemma lem4383161 {A B : Type'} (s : A -> Prop) : (term11 A B s) = (term12 A B s).
Proof. exact (eq_refl (term11 A B s)). Qed.
Lemma lem4383162 {A B : Type'} (s : A -> Prop) : term12 A B s.
Proof. exact (EQ_MP (@lem4383161 A B s) (@lem4383160 A B s)). Qed.
Lemma lem4383163 {A B : Type'} (s : A -> Prop) (f : A -> B) : term13 A B s f.
Proof. exact (@lem4383162 A B s f). Qed.
Lemma lem4383164 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term13 A B s f) = ((term14 A B f s) = (term15 A B s f)).
Proof. exact (eq_refl (term13 A B s f)). Qed.
Lemma lem4383166 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4383167 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4383168 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem4383167 A s) (@lem4383166 A s)). Qed.
Lemma lem4383169 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem4383168 A s t). Qed.
Lemma lem4383170 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem4383175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem4383170 A s t) (@lem4383169 A s t)). Qed.
Lemma lem4383176 {A B : Type'} (s : type572 A B) (t : type572 A B) : (s = t) = (term20 A B s t).
Proof. exact (@lem4383175 (A -> B) s t). Qed.
Lemma lem4383177 {A B : Type'} : ((@EXTENSIONAL A B (@EMPTY A)) = (term21 A B)) = (term22 A B).
Proof. exact (@lem4383176 A B (@EXTENSIONAL A B (@EMPTY A)) (term21 A B)). Qed.
Lemma lem4383187 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B f s) = (term15 A B s f).
Proof. exact (EQ_MP (@lem4383164 A B s f) (@lem4383163 A B s f)). Qed.
Lemma lem4383188 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B f s) = (term15 A B s f).
Proof. exact (@lem4383187 A B s f). Qed.
Lemma lem4383189 {A B : Type'} (x : A -> B) : (term23 A B x) = (term24 A B x).
Proof. exact (@lem4383188 A B (@EMPTY A) x). Qed.
Lemma lem4383197 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4383152 A x (@lem4383151 A x)). Qed.
Lemma lem4383198 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4383197 A x). Qed.
Lemma lem4383199 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4383200 {A : Type'} (x : A) : (term5 A x) = (~ False).
Proof. exact (MK_COMB (@lem4383199) (@lem4383198 A x)). Qed.
Lemma lem4383202 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4383203 {A : Type'} (x : A) : (term5 A x) = True.
Proof. exact (TRANS (@lem4383200 A x) (@lem4383202)). Qed.
Lemma lem4383204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4383205 {A : Type'} (x : A) : (term25 A x) = (imp True).
Proof. exact (MK_COMB (@lem4383204) (@lem4383203 A x)). Qed.
Lemma lem4383210 {A B : Type'} (x : A -> B) (x' : A) : ((x x') = (@ARB B)) = ((x x') = (@ARB B)).
Proof. exact (eq_refl ((x x') = (@ARB B))). Qed.
Lemma lem4383211 {A B : Type'} (x : A -> B) (x' : A) : (term26 A B x x') = (term27 A B x x').
Proof. exact (MK_COMB (@lem4383205 A x') (@lem4383210 A B x x')). Qed.
Lemma lem4383213 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4383214 {A B : Type'} (x : A -> B) (x' : A) : (term27 A B x x') = ((x x') = (@ARB B)).
Proof. exact (@lem4383213 ((x x') = (@ARB B))). Qed.
Lemma lem4383219 {A B : Type'} (x : A -> B) (x' : A) : (term26 A B x x') = ((x x') = (@ARB B)).
Proof. exact (TRANS (@lem4383211 A B x x') (@lem4383214 A B x x')). Qed.
Lemma lem4383220 {A B : Type'} (x : A -> B) : (term28 A B x) = (term29 A B x).
Proof. exact (fun_ext (fun x' : A => @lem4383219 A B x x')). Qed.
Lemma lem4383221 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383222 {A B : Type'} (x : A -> B) : (term24 A B x) = (term30 A B x).
Proof. exact (MK_COMB (@lem4383221 A) (@lem4383220 A B x)). Qed.
Lemma lem4383227 {A B : Type'} (x : A -> B) : (term23 A B x) = (term30 A B x).
Proof. exact (TRANS (@lem4383189 A B x) (@lem4383222 A B x)). Qed.
Lemma lem4383228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4383229 {A B : Type'} (x : A -> B) : (term31 A B x) = (term32 A B x).
Proof. exact (MK_COMB (@lem4383228) (@lem4383227 A B x)). Qed.
Lemma lem4383231 {A : Type'} (x : A) (y : A) : (term10 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4383158 A x y) (@lem4383157 A x y)). Qed.
Lemma lem4383232 {A B : Type'} (x : A -> B) (y : A -> B) : (term33 A B x y) = (x = y).
Proof. exact (@lem4383231 (A -> B) x y). Qed.
Lemma lem4383233 {A B : Type'} (x : A -> B) : (term34 A B x) = (x = (term35 A B)).
Proof. exact (@lem4383232 A B x (term35 A B)). Qed.
Lemma lem4383238 {A B : Type'} (x : A -> B) : ((term23 A B x) = (term34 A B x)) = ((term30 A B x) = (x = (term35 A B))).
Proof. exact (MK_COMB (@lem4383229 A B x) (@lem4383233 A B x)). Qed.
Lemma lem4383243 {A B : Type'} : (term36 A B) = (term37 A B).
Proof. exact (fun_ext (fun x : A -> B => @lem4383238 A B x)). Qed.
Lemma lem4383244 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383245 {A B : Type'} : (term22 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem4383244 A B) (@lem4383243 A B)). Qed.
Lemma lem4383250 {A B : Type'} : ((@EXTENSIONAL A B (@EMPTY A)) = (term21 A B)) = (term38 A B).
Proof. exact (TRANS (@lem4383177 A B) (@lem4383245 A B)). Qed.
Lemma lem4383251 {A B : Type'} : (term38 A B) = ((@EXTENSIONAL A B (@EMPTY A)) = (term21 A B)).
Proof. exact (SYM (@lem4383250 A B)). Qed.
Lemma lem4383271 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem4383147 A B f g) (@lem4383146 A B f g)). Qed.
Lemma lem4383272 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (@lem4383271 A B f g). Qed.
Lemma lem4383273 {A B : Type'} (x : A -> B) : (x = (term35 A B)) = (term39 A B x).
Proof. exact (@lem4383272 A B x (term35 A B)). Qed.
Lemma lem4383283 {A B : Type'} (f : A -> B) (y : A) : (term40 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4383284 {A B : Type'} (f : A -> B) (y : A) : (term40 A B f y) = (f y).
Proof. exact (@lem4383283 A B f y). Qed.
Lemma lem4383285 {A B : Type'} (x : A) : (term41 A B x) = (term42 A B x).
Proof. exact (@lem4383284 A B (term35 A B) x). Qed.
Lemma lem4383286 {A B : Type'} (x : A) : (term42 A B x) = (@ARB B).
Proof. exact (eq_refl (term42 A B x)). Qed.
Lemma lem4383287 {A B : Type'} : (term43 A B) = (term35 A B).
Proof. exact (fun_ext (fun x : A => @lem4383286 A B x)). Qed.
Lemma lem4383288 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4383289 {A B : Type'} (x : A) : (term41 A B x) = (term42 A B x).
Proof. exact (MK_COMB (@lem4383287 A B) (@lem4383288 A x)). Qed.
Lemma lem4383290 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4383291 {A B : Type'} (x : A) : (term44 A B x) = (term45 A B x).
Proof. exact (MK_COMB (@lem4383290 B) (@lem4383289 A B x)). Qed.
Lemma lem4383292 {A B : Type'} (x : A) : (term42 A B x) = (@ARB B).
Proof. exact (eq_refl (term42 A B x)). Qed.
Lemma lem4383293 {A B : Type'} (x : A) : ((term41 A B x) = (term42 A B x)) = ((term42 A B x) = (@ARB B)).
Proof. exact (MK_COMB (@lem4383291 A B x) (@lem4383292 A B x)). Qed.
Lemma lem4383294 {A B : Type'} (x : A) : (term42 A B x) = (@ARB B).
Proof. exact (EQ_MP (@lem4383293 A B x) (@lem4383285 A B x)). Qed.
Lemma lem4383295 {A B : Type'} (x : A -> B) (x' : A) : (term46 A B x x') = (term46 A B x x').
Proof. exact (eq_refl (term46 A B x x')). Qed.
Lemma lem4383296 {A B : Type'} (x : A -> B) (x' : A) : ((x x') = (term42 A B x')) = ((x x') = (@ARB B)).
Proof. exact (MK_COMB (@lem4383295 A B x x') (@lem4383294 A B x')). Qed.
Lemma lem4383301 {A B : Type'} (x : A -> B) : (term47 A B x) = (term29 A B x).
Proof. exact (fun_ext (fun x' : A => @lem4383296 A B x x')). Qed.
Lemma lem4383302 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383303 {A B : Type'} (x : A -> B) : (term39 A B x) = (term30 A B x).
Proof. exact (MK_COMB (@lem4383302 A) (@lem4383301 A B x)). Qed.
Lemma lem4383308 {A B : Type'} (x : A -> B) : (x = (term35 A B)) = (term30 A B x).
Proof. exact (TRANS (@lem4383273 A B x) (@lem4383303 A B x)). Qed.
Lemma lem4383309 {A B : Type'} (x : A -> B) : (term32 A B x) = (term32 A B x).
Proof. exact (eq_refl (term32 A B x)). Qed.
Lemma lem4383310 {A B : Type'} (x : A -> B) : ((term30 A B x) = (x = (term35 A B))) = ((term30 A B x) = (term30 A B x)).
Proof. exact (MK_COMB (@lem4383309 A B x) (@lem4383308 A B x)). Qed.
Lemma lem4383312 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4383313 (x : Prop) : (x = x) = True.
Proof. exact (@lem4383312 Prop x). Qed.
Lemma lem4383314 {A B : Type'} (x : A -> B) : ((term30 A B x) = (term30 A B x)) = True.
Proof. exact (@lem4383313 (term30 A B x)). Qed.
Lemma lem4383315 {A B : Type'} (x : A -> B) : ((term30 A B x) = (x = (term35 A B))) = True.
Proof. exact (TRANS (@lem4383310 A B x) (@lem4383314 A B x)). Qed.
Lemma lem4383316 {A B : Type'} : (term37 A B) = (term48 A B).
Proof. exact (fun_ext (fun x : A -> B => @lem4383315 A B x)). Qed.
Lemma lem4383317 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383318 {A B : Type'} : (term38 A B) = (term49 A B).
Proof. exact (MK_COMB (@lem4383317 A B) (@lem4383316 A B)). Qed.
Lemma lem4383320 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4383321 {A B : Type'} (t : Prop) : (term51 A B t) = t.
Proof. exact (@lem4383320 (A -> B) t). Qed.
Lemma lem4383322 {A B : Type'} : (term49 A B) = True.
Proof. exact (@lem4383321 A B True). Qed.
Lemma lem4383323 {A B : Type'} : (term38 A B) = True.
Proof. exact (TRANS (@lem4383318 A B) (@lem4383322 A B)). Qed.
Lemma lem4383324 {A B : Type'} : True = (term38 A B).
Proof. exact (SYM (@lem4383323 A B)). Qed.
Lemma lem4383325 {A B : Type'} : term38 A B.
Proof. exact (EQ_MP (@lem4383324 A B) (@lem0)). Qed.
Lemma lem4383326 {A B : Type'} : (@EXTENSIONAL A B (@EMPTY A)) = (term21 A B).
Proof. exact (EQ_MP (@lem4383251 A B) (@lem4383325 A B)). Qed.
