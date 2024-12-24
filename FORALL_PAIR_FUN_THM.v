Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_PAIR_FUN_THM_term_abbrevs.
Require Import ETA_AX_spec.
Require Import PAIR_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem54106 {A B : Type'} (x : prod A B) (h1 : (term0 A B x) = x) : (term0 A B x) = x.
Proof. exact (h1). Qed.
Lemma lem54107 {A B : Type'} (x : prod A B) (h1 : (term0 A B x) = x) : x = (term0 A B x).
Proof. exact (SYM (@lem54106 A B x h1)). Qed.
Lemma lem54108 {A B : Type'} (x : prod A B) (h1 : x = (term0 A B x)) : x = (term0 A B x).
Proof. exact (h1). Qed.
Lemma lem54109 {A B : Type'} (x : prod A B) (h1 : x = (term0 A B x)) : (term0 A B x) = x.
Proof. exact (SYM (@lem54108 A B x h1)). Qed.
Lemma lem54110 {A B : Type'} (x : prod A B) : ((term0 A B x) = x) = (x = (term0 A B x)).
Proof. exact (prop_ext (fun h1 : (term0 A B x) = x => @lem54107 A B x h1) (fun h1 : x = (term0 A B x) => @lem54109 A B x h1)). Qed.
Lemma lem54111 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem54110 A B x)). Qed.
Lemma lem54112 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem54113 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem54112 A B) (@lem54111 A B)). Qed.
Lemma lem54114 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem54113 A B) (@lem48081 A B)). Qed.
Lemma lem54115 {A B : Type'} (x : prod A B) : term5 A B x.
Proof. exact (@lem54114 A B x). Qed.
Lemma lem54116 {A B : Type'} (x : prod A B) : (term5 A B x) = (x = (term0 A B x)).
Proof. exact (eq_refl (term5 A B x)). Qed.
Lemma lem54119 {A B : Type'} (t : A -> B) (h1 : (term6 A B t) = t) : (term6 A B t) = t.
Proof. exact (h1). Qed.
Lemma lem54120 {A B : Type'} (t : A -> B) (h1 : (term6 A B t) = t) : t = (term6 A B t).
Proof. exact (SYM (@lem54119 A B t h1)). Qed.
Lemma lem54121 {A B : Type'} (t : A -> B) (h1 : t = (term6 A B t)) : t = (term6 A B t).
Proof. exact (h1). Qed.
Lemma lem54122 {A B : Type'} (t : A -> B) (h1 : t = (term6 A B t)) : (term6 A B t) = t.
Proof. exact (SYM (@lem54121 A B t h1)). Qed.
Lemma lem54123 {A B : Type'} (t : A -> B) : ((term6 A B t) = t) = (t = (term6 A B t)).
Proof. exact (prop_ext (fun h1 : (term6 A B t) = t => @lem54120 A B t h1) (fun h1 : t = (term6 A B t) => @lem54122 A B t h1)). Qed.
Lemma lem54124 {A B : Type'} : (term7 A B) = (term8 A B).
Proof. exact (fun_ext (fun t : A -> B => @lem54123 A B t)). Qed.
Lemma lem54125 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem54126 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem54125 A B) (@lem54124 A B)). Qed.
Lemma lem54127 {A B : Type'} : term10 A B.
Proof. exact (EQ_MP (@lem54126 A B) (@lem9121 A B)). Qed.
Lemma lem54128 {A B : Type'} (t : A -> B) : term11 A B t.
Proof. exact (@lem54127 A B t). Qed.
Lemma lem54129 {A B : Type'} (t : A -> B) : (term11 A B t) = (t = (term6 A B t)).
Proof. exact (eq_refl (term11 A B t)). Qed.
Lemma lem54131 {A B C : Type'} (P : type478 A B C) (h1 : term12 A B C P) : term12 A B C P.
Proof. exact (h1). Qed.
Lemma lem54132 {A B C : Type'} (P : type478 A B C) (h1 : term13 A B C P) : term13 A B C P.
Proof. exact (h1). Qed.
Lemma lem54133 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term12 A B C P) : term14 A B C P f.
Proof. exact (@lem54131 A B C P h1 f). Qed.
Lemma lem54134 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term14 A B C P f) = (P f).
Proof. exact (eq_refl (term14 A B C P f)). Qed.
Lemma lem54135 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term12 A B C P) : P f.
Proof. exact (EQ_MP (@lem54134 A B C P f) (@lem54133 A B C f P h1)). Qed.
Lemma lem54136 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (P f) = ((P f) = True).
Proof. exact (@lem7 (P f)). Qed.
Lemma lem54147 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term12 A B C P) : (P f) = True.
Proof. exact (EQ_MP (@lem54136 A B C P f) (@lem54135 A B C f P h1)). Qed.
Lemma lem54148 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term12 A B C P) : (P f) = True.
Proof. exact (@lem54147 A B C f P h1). Qed.
Lemma lem54149 {A B C : Type'} (g : A -> B) (h : A -> C) (P : type478 A B C) (h1 : term12 A B C P) : (term15 A B C P g h) = True.
Proof. exact (@lem54148 A B C (term16 A B C g h) P h1). Qed.
Lemma lem54150 {A B C : Type'} (g : A -> B) (P : type478 A B C) (h1 : term12 A B C P) : (term17 A B C P g) = (term18 A C).
Proof. exact (fun_ext (fun h : A -> C => @lem54149 A B C g h P h1)). Qed.
Lemma lem54151 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem54152 {A B C : Type'} (g : A -> B) (P : type478 A B C) (h1 : term12 A B C P) : (term19 A B C P g) = (term20 A C).
Proof. exact (MK_COMB (@lem54151 A C) (@lem54150 A B C g P h1)). Qed.
Lemma lem54154 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem54155 {A C : Type'} (t : Prop) : (term22 A C t) = t.
Proof. exact (@lem54154 (A -> C) t). Qed.
Lemma lem54156 {A C : Type'} : (term20 A C) = True.
Proof. exact (@lem54155 A C True). Qed.
Lemma lem54157 {A B C : Type'} (g : A -> B) (P : type478 A B C) (h1 : term12 A B C P) : (term19 A B C P g) = True.
Proof. exact (TRANS (@lem54152 A B C g P h1) (@lem54156 A C)). Qed.
Lemma lem54158 {A B C : Type'} (P : type478 A B C) (h1 : term12 A B C P) : (term23 A B C P) = (term18 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem54157 A B C g P h1)). Qed.
Lemma lem54159 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem54160 {A B C : Type'} (P : type478 A B C) (h1 : term12 A B C P) : (term13 A B C P) = (term20 A B).
Proof. exact (MK_COMB (@lem54159 A B) (@lem54158 A B C P h1)). Qed.
Lemma lem54162 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem54163 {A B : Type'} (t : Prop) : (term22 A B t) = t.
Proof. exact (@lem54162 (A -> B) t). Qed.
Lemma lem54164 {A B : Type'} : (term20 A B) = True.
Proof. exact (@lem54163 A B True). Qed.
Lemma lem54165 {A B C : Type'} (P : type478 A B C) (h1 : term12 A B C P) : (term13 A B C P) = True.
Proof. exact (TRANS (@lem54160 A B C P h1) (@lem54164 A B)). Qed.
Lemma lem54166 {A B C : Type'} (P : type478 A B C) (h1 : term12 A B C P) : True = (term13 A B C P).
Proof. exact (SYM (@lem54165 A B C P h1)). Qed.
Lemma lem54167 {A B C : Type'} (P : type478 A B C) (h1 : term12 A B C P) : term13 A B C P.
Proof. exact (EQ_MP (@lem54166 A B C P h1) (@lem0)). Qed.
Lemma lem54183 {A B : Type'} (t : A -> B) : t = (term6 A B t).
Proof. exact (EQ_MP (@lem54129 A B t) (@lem54128 A B t)). Qed.
Lemma lem54184 {A B C : Type'} (t : type1430 A B C) : t = (term24 A B C t).
Proof. exact (@lem54183 A (prod B C) t). Qed.
Lemma lem54185 {A B C : Type'} (f : type1430 A B C) : f = (term24 A B C f).
Proof. exact (@lem54184 A B C f). Qed.
Lemma lem54186 {A B C : Type'} (P : type478 A B C) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem54187 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (P f) = (term25 A B C P f).
Proof. exact (MK_COMB (@lem54186 A B C P) (@lem54185 A B C f)). Qed.
Lemma lem54188 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term25 A B C P f) = (P f).
Proof. exact (SYM (@lem54187 A B C P f)). Qed.
Lemma lem54190 {A B : Type'} (x : prod A B) : x = (term0 A B x).
Proof. exact (EQ_MP (@lem54116 A B x) (@lem54115 A B x)). Qed.
Lemma lem54191 {B C : Type'} (x : prod B C) : x = (term0 B C x).
Proof. exact (@lem54190 B C x). Qed.
Lemma lem54192 {A B C : Type'} (f : type1430 A B C) (x : A) : (f x) = (term26 A B C f x).
Proof. exact (@lem54191 B C (f x)). Qed.
Lemma lem54193 {A B C : Type'} (f : type1430 A B C) : (term24 A B C f) = (term27 A B C f).
Proof. exact (fun_ext (fun x : A => @lem54192 A B C f x)). Qed.
Lemma lem54194 {A B C : Type'} (P : type478 A B C) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem54195 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term25 A B C P f) = (term28 A B C P f).
Proof. exact (MK_COMB (@lem54194 A B C P) (@lem54193 A B C f)). Qed.
Lemma lem54196 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term28 A B C P f) = (term25 A B C P f).
Proof. exact (SYM (@lem54195 A B C P f)). Qed.
Lemma lem54197 {A B C : Type'} (g : A -> B) (P : type478 A B C) (h1 : term13 A B C P) : term29 A B C P g.
Proof. exact (@lem54132 A B C P h1 g). Qed.
Lemma lem54198 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term29 A B C P g) = (term19 A B C P g).
Proof. exact (eq_refl (term29 A B C P g)). Qed.
Lemma lem54199 {A B C : Type'} (g : A -> B) (P : type478 A B C) (h1 : term13 A B C P) : term19 A B C P g.
Proof. exact (EQ_MP (@lem54198 A B C P g) (@lem54197 A B C g P h1)). Qed.
Lemma lem54200 {A B C : Type'} (g : A -> B) (h : A -> C) (P : type478 A B C) (h1 : term13 A B C P) : term30 A B C P g h.
Proof. exact (@lem54199 A B C g P h1 h). Qed.
Lemma lem54201 {A B C : Type'} (P : type478 A B C) (g : A -> B) (h : A -> C) : (term30 A B C P g h) = (term15 A B C P g h).
Proof. exact (eq_refl (term30 A B C P g h)). Qed.
Lemma lem54202 {A B C : Type'} (g : A -> B) (h : A -> C) (P : type478 A B C) (h1 : term13 A B C P) : term15 A B C P g h.
Proof. exact (EQ_MP (@lem54201 A B C P g h) (@lem54200 A B C g h P h1)). Qed.
Lemma lem54203 {A B C : Type'} (P : type478 A B C) (g : A -> B) (h : A -> C) : (term15 A B C P g h) = ((term15 A B C P g h) = True).
Proof. exact (@lem7 (term15 A B C P g h)). Qed.
Lemma lem54206 {A B C : Type'} (g : A -> B) (h : A -> C) (P : type478 A B C) (h1 : term13 A B C P) : (term15 A B C P g h) = True.
Proof. exact (EQ_MP (@lem54203 A B C P g h) (@lem54202 A B C g h P h1)). Qed.
Lemma lem54207 {A B C : Type'} (g : A -> B) (h : A -> C) (P : type478 A B C) (h1 : term13 A B C P) : (term15 A B C P g h) = True.
Proof. exact (@lem54206 A B C g h P h1). Qed.
Lemma lem54208 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term13 A B C P) : (term31 A B C P f) = True.
Proof. exact (@lem54207 A B C (term32 A B C f) (term33 A B C f) P h1). Qed.
Lemma lem54209 {A B C : Type'} (f : type1430 A B C) (x : A) : (term34 A B C f x) = (term35 A B C f x).
Proof. exact (eq_refl (term34 A B C f x)). Qed.
Lemma lem54210 {B C : Type'} : (@pair B C) = (@pair B C).
Proof. exact (eq_refl (@pair B C)). Qed.
Lemma lem54211 {A B C : Type'} (f : type1430 A B C) (x : A) : (term36 A B C f x) = (term37 A B C f x).
Proof. exact (MK_COMB (@lem54210 B C) (@lem54209 A B C f x)). Qed.
Lemma lem54212 {A B C : Type'} (f : type1430 A B C) (x : A) : (term38 A B C f x) = (term39 A B C f x).
Proof. exact (eq_refl (term38 A B C f x)). Qed.
Lemma lem54213 {A B C : Type'} (f : type1430 A B C) (x : A) : (term40 A B C f x) = (term26 A B C f x).
Proof. exact (MK_COMB (@lem54211 A B C f x) (@lem54212 A B C f x)). Qed.
Lemma lem54214 {A B C : Type'} (f : type1430 A B C) : (term41 A B C f) = (term27 A B C f).
Proof. exact (fun_ext (fun x : A => @lem54213 A B C f x)). Qed.
Lemma lem54215 {A B C : Type'} (P : type478 A B C) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem54216 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term31 A B C P f) = (term28 A B C P f).
Proof. exact (MK_COMB (@lem54215 A B C P) (@lem54214 A B C f)). Qed.
Lemma lem54217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54218 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term42 A B C P f) = (term43 A B C P f).
Proof. exact (MK_COMB (@lem54217) (@lem54216 A B C P f)). Qed.
Lemma lem54219 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem54220 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : ((term31 A B C P f) = True) = ((term28 A B C P f) = True).
Proof. exact (MK_COMB (@lem54218 A B C P f) (@lem54219)). Qed.
Lemma lem54221 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term13 A B C P) : (term28 A B C P f) = True.
Proof. exact (EQ_MP (@lem54220 A B C P f) (@lem54208 A B C f P h1)). Qed.
Lemma lem54222 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term13 A B C P) : True = (term28 A B C P f).
Proof. exact (SYM (@lem54221 A B C f P h1)). Qed.
Lemma lem54223 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term13 A B C P) : term28 A B C P f.
Proof. exact (EQ_MP (@lem54222 A B C f P h1) (@lem0)). Qed.
Lemma lem54224 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term13 A B C P) : term25 A B C P f.
Proof. exact (EQ_MP (@lem54196 A B C P f) (@lem54223 A B C f P h1)). Qed.
Lemma lem54225 {A B C : Type'} (f : type1430 A B C) (P : type478 A B C) (h1 : term13 A B C P) : P f.
Proof. exact (EQ_MP (@lem54188 A B C P f) (@lem54224 A B C f P h1)). Qed.
Lemma lem54231 {A B C : Type'} (P : type478 A B C) (h1 : term13 A B C P) : term12 A B C P.
Proof. exact (fun f : type1430 A B C => @lem54225 A B C f P h1). Qed.
Lemma lem54232 {A B C : Type'} (P : type478 A B C) : term44 A B C P.
Proof. exact (fun h0 : term13 A B C P => @lem54231 A B C P h0). Qed.
Lemma lem54233 {A B C : Type'} (P : type478 A B C) : term45 A B C P.
Proof. exact (fun h0 : term12 A B C P => @lem54167 A B C P h0). Qed.
Lemma lem54234 {A B C : Type'} (P : type478 A B C) : term46 A B C P.
Proof. exact (conj (@lem54233 A B C P) (@lem54232 A B C P)). Qed.
Lemma lem54235 {A B C : Type'} (P : type478 A B C) : (term46 A B C P) = ((term12 A B C P) = (term13 A B C P)).
Proof. exact (@lem32 (term12 A B C P) (term13 A B C P)). Qed.
Lemma lem54236 {A B C : Type'} (P : type478 A B C) : (term12 A B C P) = (term13 A B C P).
Proof. exact (EQ_MP (@lem54235 A B C P) (@lem54234 A B C P)). Qed.
Lemma lem54241 {A B C : Type'} : term47 A B C.
Proof. exact (fun P : type478 A B C => @lem54236 A B C P). Qed.
