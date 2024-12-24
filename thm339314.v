Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm339314_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm322939_spec.
Require Import thm339112_spec.
Require Import thm7_spec.
Lemma lem339114 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : @WF A lt2.
Proof. exact (h1). Qed.
Lemma lem339115 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term0 A B lt2 H.
Proof. exact (h1). Qed.
Lemma lem339119 {A B : Type'} (lt2 : type1402 A) : term1 A B lt2.
Proof. exact (EQ_MP (@lem322939 A B lt2) (@lem339112 A B lt2)). Qed.
Lemma lem339120 {A B : Type'} (lt2 : type1402 A) : term1 A B lt2.
Proof. exact (@lem339119 A B lt2). Qed.
Lemma lem339121 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term2 A B lt2.
Proof. exact (@lem339120 A B lt2 (@lem339114 A lt2 h1)). Qed.
Lemma lem339122 {A B : Type'} (lt2 : type1402 A) (h1 : term2 A B lt2) : term2 A B lt2.
Proof. exact (h1). Qed.
Lemma lem339123 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term2 A B lt2) : term3 A B lt2 H.
Proof. exact (@lem339122 A B lt2 h1 H). Qed.
Lemma lem339124 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term3 A B lt2 H) = (term4 A B lt2 H).
Proof. exact (eq_refl (term3 A B lt2 H)). Qed.
Lemma lem339125 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term2 A B lt2) : term4 A B lt2 H.
Proof. exact (EQ_MP (@lem339124 A B lt2 H) (@lem339123 A B H lt2 h1)). Qed.
Lemma lem339126 {A B : Type'} (H : type549 A B) (S' : type1413 A B) (lt2 : type1402 A) (h1 : term2 A B lt2) : term5 A B lt2 H S'.
Proof. exact (@lem339125 A B H lt2 h1 S'). Qed.
Lemma lem339127 {A B : Type'} (lt2 : type1402 A) (S' : type1413 A B) (H : type549 A B) : (term5 A B lt2 H S') = (term6 A B lt2 S' H).
Proof. exact (eq_refl (term5 A B lt2 H S')). Qed.
Lemma lem339128 {A B : Type'} (S' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term2 A B lt2) : term6 A B lt2 S' H.
Proof. exact (EQ_MP (@lem339127 A B lt2 S' H) (@lem339126 A B H S' lt2 h1)). Qed.
Lemma lem339129 {A B : Type'} (lt2 : type1402 A) (S' : type1413 A B) (H : type549 A B) (h1 : term7 A B lt2 S' H) : term7 A B lt2 S' H.
Proof. exact (h1). Qed.
Lemma lem339130 {A B : Type'} (S' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term7 A B lt2 S' H) (h2 : term2 A B lt2) : term8 A B H.
Proof. exact (@lem339128 A B S' H lt2 h2 (@lem339129 A B lt2 S' H h1)). Qed.
Lemma lem339131 {A B : Type'} (lt2 : type1402 A) (S' : type1413 A B) (H : type549 A B) (h1 : term7 A B lt2 S' H) : term9 A B lt2 H.
Proof. exact (fun h0 : term2 A B lt2 => @lem339130 A B S' H lt2 h1 h0). Qed.
Lemma lem339132 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term10 A B lt2 H.
Proof. exact (h1). Qed.
Lemma lem339133 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term9 A B lt2 H.
Proof. exact (ex_elim (@lem339132 A B lt2 H h1) (fun S' : type1413 A B => fun h0 : term11 A B lt2 H S' => @lem339131 A B lt2 S' H h0)). Qed.
Lemma lem339134 {A B : Type'} (lt2 : type1402 A) (h1 : term2 A B lt2) : term2 A B lt2.
Proof. exact (h1). Qed.
Lemma lem339135 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term2 A B lt2) (h2 : term10 A B lt2 H) : term8 A B H.
Proof. exact (@lem339133 A B lt2 H h2 (@lem339134 A B lt2 h1)). Qed.
Lemma lem339136 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term2 A B lt2) : term12 A B lt2 H.
Proof. exact (fun h0 : term10 A B lt2 H => @lem339135 A B lt2 H h1 h0). Qed.
Lemma lem339137 {A B : Type'} (lt2 : type1402 A) (h1 : term2 A B lt2) : term13 A B lt2.
Proof. exact (fun H : type549 A B => @lem339136 A B H lt2 h1). Qed.
Lemma lem339138 {A B : Type'} (lt2 : type1402 A) : term14 A B lt2.
Proof. exact (fun h0 : term2 A B lt2 => @lem339137 A B lt2 h0). Qed.
Lemma lem339139 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term13 A B lt2.
Proof. exact (@lem339138 A B lt2 (@lem339121 A B lt2 h1)). Qed.
Lemma lem339140 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term15 A B lt2 H.
Proof. exact (@lem339139 A B lt2 h1 H). Qed.
Lemma lem339141 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term15 A B lt2 H) = (term12 A B lt2 H).
Proof. exact (eq_refl (term15 A B lt2 H)). Qed.
Lemma lem339144 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term12 A B lt2 H.
Proof. exact (EQ_MP (@lem339141 A B lt2 H) (@lem339140 A B H lt2 h1)). Qed.
Lemma lem339145 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term12 A B lt2 H.
Proof. exact (@lem339144 A B H lt2 h1). Qed.
Lemma lem339146 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term16 A B lt2 H f.
Proof. exact (@lem339115 A B lt2 H h1 f). Qed.
Lemma lem339147 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term16 A B lt2 H f) = (term17 A B lt2 f H).
Proof. exact (eq_refl (term16 A B lt2 H f)). Qed.
Lemma lem339148 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term17 A B lt2 f H.
Proof. exact (EQ_MP (@lem339147 A B lt2 f H) (@lem339146 A B f lt2 H h1)). Qed.
Lemma lem339149 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term18 A B lt2 f H g.
Proof. exact (@lem339148 A B f lt2 H h1 g). Qed.
Lemma lem339150 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term18 A B lt2 f H g) = (term19 A B lt2 f H g).
Proof. exact (eq_refl (term18 A B lt2 f H g)). Qed.
Lemma lem339151 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term19 A B lt2 f H g.
Proof. exact (EQ_MP (@lem339150 A B lt2 f H g) (@lem339149 A B f g lt2 H h1)). Qed.
Lemma lem339152 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term20 A B lt2 f H g x.
Proof. exact (@lem339151 A B f g lt2 H h1 x). Qed.
Lemma lem339153 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term20 A B lt2 f H g x) = (term21 A B lt2 f H g x).
Proof. exact (eq_refl (term20 A B lt2 f H g x)). Qed.
Lemma lem339154 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term21 A B lt2 f H g x.
Proof. exact (EQ_MP (@lem339153 A B lt2 f H g x) (@lem339152 A B f g x lt2 H h1)). Qed.
Lemma lem339155 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term21 A B lt2 f H g x) = ((term21 A B lt2 f H g x) = True).
Proof. exact (@lem7 (term21 A B lt2 f H g x)). Qed.
Lemma lem339182 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem339183 {A B : Type'} (f : type1413 A B) (y : A) : (term23 A B f y) = (f y).
Proof. exact (@lem339182 A (B -> Prop) f y). Qed.
Lemma lem339184 {A B : Type'} (z : A) : (term24 A B z) = (term25 A B z).
Proof. exact (@lem339183 A B (term26 A B) z). Qed.
Lemma lem339185 {A B : Type'} (x : A) : (term25 A B x) = (term27 B).
Proof. exact (eq_refl (term25 A B x)). Qed.
Lemma lem339186 {A B : Type'} : (term28 A B) = (term26 A B).
Proof. exact (fun_ext (fun x : A => @lem339185 A B x)). Qed.
Lemma lem339187 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem339188 {A B : Type'} (z : A) : (term24 A B z) = (term25 A B z).
Proof. exact (MK_COMB (@lem339186 A B) (@lem339187 A z)). Qed.
Lemma lem339189 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem339190 {A B : Type'} (z : A) : (term29 A B z) = (term30 A B z).
Proof. exact (MK_COMB (@lem339189 B) (@lem339188 A B z)). Qed.
Lemma lem339191 {A B : Type'} (z : A) : (term25 A B z) = (term27 B).
Proof. exact (eq_refl (term25 A B z)). Qed.
Lemma lem339192 {A B : Type'} (z : A) : ((term24 A B z) = (term25 A B z)) = ((term25 A B z) = (term27 B)).
Proof. exact (MK_COMB (@lem339190 A B z) (@lem339191 A B z)). Qed.
Lemma lem339193 {A B : Type'} (z : A) : (term25 A B z) = (term27 B).
Proof. exact (EQ_MP (@lem339192 A B z) (@lem339184 A B z)). Qed.
Lemma lem339194 {A B : Type'} (f : A -> B) (z : A) : (f z) = (f z).
Proof. exact (eq_refl (f z)). Qed.
Lemma lem339195 {A B : Type'} (f : A -> B) (z : A) : (term31 A B f z) = (term32 A B f z).
Proof. exact (MK_COMB (@lem339193 A B z) (@lem339194 A B f z)). Qed.
Lemma lem339197 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem339198 {B : Type'} (f : B -> Prop) (y : B) : (term33 B f y) = (f y).
Proof. exact (@lem339197 B Prop f y). Qed.
Lemma lem339199 {A B : Type'} (f : A -> B) (z : A) : (term34 A B f z) = (term32 A B f z).
Proof. exact (@lem339198 B (term27 B) (f z)). Qed.
Lemma lem339200 {B : Type'} (y : B) : (term35 B y) = True.
Proof. exact (eq_refl (term35 B y)). Qed.
Lemma lem339201 {B : Type'} : (term36 B) = (term27 B).
Proof. exact (fun_ext (fun y : B => @lem339200 B y)). Qed.
Lemma lem339202 {A B : Type'} (f : A -> B) (z : A) : (f z) = (f z).
Proof. exact (eq_refl (f z)). Qed.
Lemma lem339203 {A B : Type'} (f : A -> B) (z : A) : (term34 A B f z) = (term32 A B f z).
Proof. exact (MK_COMB (@lem339201 B) (@lem339202 A B f z)). Qed.
Lemma lem339204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339205 {A B : Type'} (f : A -> B) (z : A) : (term37 A B f z) = (term38 A B f z).
Proof. exact (MK_COMB (@lem339204) (@lem339203 A B f z)). Qed.
Lemma lem339206 {A B : Type'} (f : A -> B) (z : A) : (term32 A B f z) = True.
Proof. exact (eq_refl (term32 A B f z)). Qed.
Lemma lem339207 {A B : Type'} (f : A -> B) (z : A) : ((term34 A B f z) = (term32 A B f z)) = ((term32 A B f z) = True).
Proof. exact (MK_COMB (@lem339205 A B f z) (@lem339206 A B f z)). Qed.
Lemma lem339208 {A B : Type'} (f : A -> B) (z : A) : (term32 A B f z) = True.
Proof. exact (EQ_MP (@lem339207 A B f z) (@lem339199 A B f z)). Qed.
Lemma lem339209 {A B : Type'} (f : A -> B) (z : A) : (term31 A B f z) = True.
Proof. exact (TRANS (@lem339195 A B f z) (@lem339208 A B f z)). Qed.
Lemma lem339210 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : (term39 A B f g z) = (term39 A B f g z).
Proof. exact (eq_refl (term39 A B f g z)). Qed.
Lemma lem339211 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : (term40 A B g f z) = (term41 A B f g z).
Proof. exact (MK_COMB (@lem339210 A B f g z) (@lem339209 A B f z)). Qed.
Lemma lem339213 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem339214 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : (term41 A B f g z) = ((f z) = (g z)).
Proof. exact (@lem339213 ((f z) = (g z))). Qed.
Lemma lem339217 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : (term40 A B g f z) = ((f z) = (g z)).
Proof. exact (TRANS (@lem339211 A B f g z) (@lem339214 A B f g z)). Qed.
Lemma lem339218 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term42 A lt2 z x) = (term42 A lt2 z x).
Proof. exact (eq_refl (term42 A lt2 z x)). Qed.
Lemma lem339219 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term43 A B lt2 x g f z) = (term44 A B lt2 x f g z).
Proof. exact (MK_COMB (@lem339218 A lt2 z x) (@lem339217 A B f g z)). Qed.
Lemma lem339222 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term45 A B lt2 x g f) = (term46 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem339219 A B lt2 x f g z)). Qed.
Lemma lem339223 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339224 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term47 A B lt2 x g f) = (term48 A B lt2 x f g).
Proof. exact (MK_COMB (@lem339223 A) (@lem339222 A B lt2 x f g)). Qed.
Lemma lem339229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem339230 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term49 A B lt2 x g f) = (term50 A B lt2 x f g).
Proof. exact (MK_COMB (@lem339229) (@lem339224 A B lt2 x f g)). Qed.
Lemma lem339236 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem339237 {A B : Type'} (f : type1413 A B) (y : A) : (term23 A B f y) = (f y).
Proof. exact (@lem339236 A (B -> Prop) f y). Qed.
Lemma lem339238 {A B : Type'} (x : A) : (term24 A B x) = (term25 A B x).
Proof. exact (@lem339237 A B (term26 A B) x). Qed.
Lemma lem339239 {A B : Type'} (x : A) : (term25 A B x) = (term27 B).
Proof. exact (eq_refl (term25 A B x)). Qed.
Lemma lem339240 {A B : Type'} : (term28 A B) = (term26 A B).
Proof. exact (fun_ext (fun x : A => @lem339239 A B x)). Qed.
Lemma lem339241 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem339242 {A B : Type'} (x : A) : (term24 A B x) = (term25 A B x).
Proof. exact (MK_COMB (@lem339240 A B) (@lem339241 A x)). Qed.
Lemma lem339243 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem339244 {A B : Type'} (x : A) : (term29 A B x) = (term30 A B x).
Proof. exact (MK_COMB (@lem339243 B) (@lem339242 A B x)). Qed.
Lemma lem339245 {A B : Type'} (x : A) : (term25 A B x) = (term27 B).
Proof. exact (eq_refl (term25 A B x)). Qed.
Lemma lem339246 {A B : Type'} (x : A) : ((term24 A B x) = (term25 A B x)) = ((term25 A B x) = (term27 B)).
Proof. exact (MK_COMB (@lem339244 A B x) (@lem339245 A B x)). Qed.
Lemma lem339247 {A B : Type'} (x : A) : (term25 A B x) = (term27 B).
Proof. exact (EQ_MP (@lem339246 A B x) (@lem339238 A B x)). Qed.
Lemma lem339248 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (H f x) = (H f x).
Proof. exact (eq_refl (H f x)). Qed.
Lemma lem339249 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term51 A B H f x) = (term52 A B H f x).
Proof. exact (MK_COMB (@lem339247 A B x) (@lem339248 A B H f x)). Qed.
Lemma lem339251 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem339252 {B : Type'} (f : B -> Prop) (y : B) : (term33 B f y) = (f y).
Proof. exact (@lem339251 B Prop f y). Qed.
Lemma lem339253 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term53 A B H f x) = (term52 A B H f x).
Proof. exact (@lem339252 B (term27 B) (H f x)). Qed.
Lemma lem339254 {B : Type'} (y : B) : (term35 B y) = True.
Proof. exact (eq_refl (term35 B y)). Qed.
Lemma lem339255 {B : Type'} : (term36 B) = (term27 B).
Proof. exact (fun_ext (fun y : B => @lem339254 B y)). Qed.
Lemma lem339256 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (H f x) = (H f x).
Proof. exact (eq_refl (H f x)). Qed.
Lemma lem339257 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term53 A B H f x) = (term52 A B H f x).
Proof. exact (MK_COMB (@lem339255 B) (@lem339256 A B H f x)). Qed.
Lemma lem339258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem339259 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term54 A B H f x) = (term55 A B H f x).
Proof. exact (MK_COMB (@lem339258) (@lem339257 A B H f x)). Qed.
Lemma lem339260 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term52 A B H f x) = True.
Proof. exact (eq_refl (term52 A B H f x)). Qed.
Lemma lem339261 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : ((term53 A B H f x) = (term52 A B H f x)) = ((term52 A B H f x) = True).
Proof. exact (MK_COMB (@lem339259 A B H f x) (@lem339260 A B H f x)). Qed.
Lemma lem339262 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term52 A B H f x) = True.
Proof. exact (EQ_MP (@lem339261 A B H f x) (@lem339253 A B H f x)). Qed.
Lemma lem339263 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term51 A B H f x) = True.
Proof. exact (TRANS (@lem339249 A B H f x) (@lem339262 A B H f x)). Qed.
Lemma lem339264 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term56 A B f H g x) = (term56 A B f H g x).
Proof. exact (eq_refl (term56 A B f H g x)). Qed.
Lemma lem339265 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term57 A B g H f x) = (term58 A B f H g x).
Proof. exact (MK_COMB (@lem339264 A B f H g x) (@lem339263 A B H f x)). Qed.
Lemma lem339267 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem339268 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term58 A B f H g x) = ((H f x) = (H g x)).
Proof. exact (@lem339267 ((H f x) = (H g x))). Qed.
Lemma lem339271 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term57 A B g H f x) = ((H f x) = (H g x)).
Proof. exact (TRANS (@lem339265 A B f H g x) (@lem339268 A B f H g x)). Qed.
Lemma lem339272 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term59 A B lt2 g H f x) = (term21 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem339230 A B lt2 x f g) (@lem339271 A B f H g x)). Qed.
Lemma lem339274 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term21 A B lt2 f H g x) = True.
Proof. exact (EQ_MP (@lem339155 A B lt2 f H g x) (@lem339154 A B f g x lt2 H h1)). Qed.
Lemma lem339275 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term21 A B lt2 f H g x) = True.
Proof. exact (@lem339274 A B f g x lt2 H h1). Qed.
Lemma lem339276 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term59 A B lt2 g H f x) = True.
Proof. exact (TRANS (@lem339272 A B lt2 f H g x) (@lem339275 A B f g x lt2 H h1)). Qed.
Lemma lem339277 {A B : Type'} (g : A -> B) (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term60 A B lt2 g H f) = (term27 A).
Proof. exact (fun_ext (fun x : A => @lem339276 A B g f x lt2 H h1)). Qed.
Lemma lem339278 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem339279 {A B : Type'} (g : A -> B) (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term61 A B lt2 g H f) = (term62 A).
Proof. exact (MK_COMB (@lem339278 A) (@lem339277 A B g f lt2 H h1)). Qed.
Lemma lem339281 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem339282 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (@lem339281 A t). Qed.
Lemma lem339283 {A : Type'} : (term62 A) = True.
Proof. exact (@lem339282 A True). Qed.
Lemma lem339284 {A B : Type'} (g : A -> B) (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term61 A B lt2 g H f) = True.
Proof. exact (TRANS (@lem339279 A B g f lt2 H h1) (@lem339283 A)). Qed.
Lemma lem339285 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term64 A B lt2 H f) = (term65 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem339284 A B g f lt2 H h1)). Qed.
Lemma lem339286 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem339287 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term66 A B lt2 H f) = (term67 A B).
Proof. exact (MK_COMB (@lem339286 A B) (@lem339285 A B f lt2 H h1)). Qed.
Lemma lem339289 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem339290 {A B : Type'} (t : Prop) : (term68 A B t) = t.
Proof. exact (@lem339289 (A -> B) t). Qed.
Lemma lem339291 {A B : Type'} : (term67 A B) = True.
Proof. exact (@lem339290 A B True). Qed.
Lemma lem339292 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term66 A B lt2 H f) = True.
Proof. exact (TRANS (@lem339287 A B f lt2 H h1) (@lem339291 A B)). Qed.
Lemma lem339293 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term69 A B lt2 H) = (term65 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem339292 A B f lt2 H h1)). Qed.
Lemma lem339294 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem339295 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term70 A B lt2 H) = (term67 A B).
Proof. exact (MK_COMB (@lem339294 A B) (@lem339293 A B lt2 H h1)). Qed.
Lemma lem339297 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem339298 {A B : Type'} (t : Prop) : (term68 A B t) = t.
Proof. exact (@lem339297 (A -> B) t). Qed.
Lemma lem339299 {A B : Type'} : (term67 A B) = True.
Proof. exact (@lem339298 A B True). Qed.
Lemma lem339300 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : (term70 A B lt2 H) = True.
Proof. exact (TRANS (@lem339295 A B lt2 H h1) (@lem339299 A B)). Qed.
Lemma lem339301 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : True = (term70 A B lt2 H).
Proof. exact (SYM (@lem339300 A B lt2 H h1)). Qed.
Lemma lem339302 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term70 A B lt2 H.
Proof. exact (EQ_MP (@lem339301 A B lt2 H h1) (@lem0)). Qed.
Lemma lem339303 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term0 A B lt2 H) : term10 A B lt2 H.
Proof. exact (ex_intro (term11 A B lt2 H) (term26 A B) (@lem339302 A B lt2 H h1)). Qed.
Lemma lem339304 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term0 A B lt2 H) (h2 : @WF A lt2) : term8 A B H.
Proof. exact (@lem339145 A B H lt2 h2 (@lem339303 A B lt2 H h1)). Qed.
Lemma lem339305 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term0 A B lt2 H) (h2 : @WF A lt2) : (term0 A B lt2 H) = (term8 A B H).
Proof. exact (prop_ext (fun h3 : term0 A B lt2 H => @lem339304 A B H lt2 h1 h2) (fun h3 : term8 A B H => @lem339115 A B lt2 H h1)). Qed.
Lemma lem339306 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term0 A B lt2 H) (h2 : @WF A lt2) : term8 A B H.
Proof. exact (EQ_MP (@lem339305 A B H lt2 h1 h2) (@lem339115 A B lt2 H h1)). Qed.
Lemma lem339307 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term71 A B lt2 H.
Proof. exact (fun h0 : term0 A B lt2 H => @lem339306 A B H lt2 h0 h1). Qed.
Lemma lem339312 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term72 A B lt2.
Proof. exact (fun H : type549 A B => @lem339307 A B H lt2 h1). Qed.
Lemma lem339313 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : (@WF A lt2) = (term72 A B lt2).
Proof. exact (prop_ext (fun h2 : @WF A lt2 => @lem339312 A B lt2 h1) (fun h2 : term72 A B lt2 => @lem339114 A lt2 h1)). Qed.
Lemma lem339314 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term72 A B lt2.
Proof. exact (EQ_MP (@lem339313 A B lt2 h1) (@lem339114 A lt2 h1)). Qed.
