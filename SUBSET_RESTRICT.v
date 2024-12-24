Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_RESTRICT_term_abbrevs.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem3221045 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3221046 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem3221045 _83095 p). Qed.
Lemma lem3221047 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem3221048 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem3221047 _83095 p) (@lem3221046 _83095 p)). Qed.
Lemma lem3221049 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem3221048 _83095 p x). Qed.
Lemma lem3221050 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem3221059 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem3221060 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem3221061 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (EQ_MP (@lem3221060 A s) (@lem3221059 A s)). Qed.
Lemma lem3221062 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term7 A s t.
Proof. exact (@lem3221061 A s t). Qed.
Lemma lem3221063 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = ((@SUBSET A s t) = (term8 A s t)).
Proof. exact (eq_refl (term7 A s t)). Qed.
Lemma lem3221074 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3221063 A s t) (@lem3221062 A s t)). Qed.
Lemma lem3221075 {_84465 : Type'} (s : _84465 -> Prop) (t : _84465 -> Prop) : (@SUBSET _84465 s t) = (term8 _84465 s t).
Proof. exact (@lem3221074 _84465 s t). Qed.
Lemma lem3221076 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term9 _84465 P s) = (term10 _84465 P s).
Proof. exact (@lem3221075 _84465 (term11 _84465 s P) s). Qed.
Lemma lem3221084 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3221085 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem3221084 p q p' q'). Qed.
Lemma lem3221086 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem3221085 p q p'). Qed.
Lemma lem3221087 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) : term15 _84465 P x s.
Proof. exact (@lem3221086 (term16 _84465 x s P) (@IN _84465 x s)). Qed.
Lemma lem3221088 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) (p' : Prop) : term17 _84465 P x s p'.
Proof. exact (@lem3221087 _84465 P x s p'). Qed.
Lemma lem3221089 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) (p' : Prop) : (term17 _84465 P x s p') = (term18 _84465 P x s p').
Proof. exact (eq_refl (term17 _84465 P x s p')). Qed.
Lemma lem3221090 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) (p' : Prop) : term18 _84465 P x s p'.
Proof. exact (EQ_MP (@lem3221089 _84465 P x s p') (@lem3221088 _84465 P x s p')). Qed.
Lemma lem3221091 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) (p' : Prop) (q' : Prop) : term19 _84465 P x s p' q'.
Proof. exact (@lem3221090 _84465 P x s p' q'). Qed.
Lemma lem3221092 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) (p' : Prop) (q' : Prop) : (term19 _84465 P x s p' q') = (term20 _84465 P x s p' q').
Proof. exact (eq_refl (term19 _84465 P x s p' q')). Qed.
Lemma lem3221093 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) (p' : Prop) (q' : Prop) : term20 _84465 P x s p' q'.
Proof. exact (EQ_MP (@lem3221092 _84465 P x s p' q') (@lem3221091 _84465 P x s p' q')). Qed.
Lemma lem3221095 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3221050 _83095 p x) (@lem3221049 _83095 p x)). Qed.
Lemma lem3221096 {_84465 : Type'} (p : _84465 -> Prop) (x : _84465) : (term4 _84465 x p) = (p x).
Proof. exact (@lem3221095 _84465 p x). Qed.
Lemma lem3221097 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term21 _84465 x s P) = (term22 _84465 s P x).
Proof. exact (@lem3221096 _84465 (term23 _84465 s P) x). Qed.
Lemma lem3221098 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term22 _84465 s P x) = (term24 _84465 s P x).
Proof. exact (eq_refl (term22 _84465 s P x)). Qed.
Lemma lem3221099 {_84465 : Type'} (GEN_PVAR_11 : _84465) : (@SETSPEC _84465 GEN_PVAR_11) = (@SETSPEC _84465 GEN_PVAR_11).
Proof. exact (eq_refl (@SETSPEC _84465 GEN_PVAR_11)). Qed.
Lemma lem3221100 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term25 _84465 GEN_PVAR_11 s P x) = (term26 _84465 GEN_PVAR_11 s P x).
Proof. exact (MK_COMB (@lem3221099 _84465 GEN_PVAR_11) (@lem3221098 _84465 s P x)). Qed.
Lemma lem3221101 {_84465 : Type'} (x : _84465) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3221102 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term27 _84465 GEN_PVAR_11 s P x) = (term28 _84465 GEN_PVAR_11 s P x).
Proof. exact (MK_COMB (@lem3221100 _84465 GEN_PVAR_11 s P x) (@lem3221101 _84465 x)). Qed.
Lemma lem3221103 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term29 _84465 GEN_PVAR_11 s P) = (term30 _84465 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3221102 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3221104 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3221105 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term31 _84465 GEN_PVAR_11 s P) = (term32 _84465 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3221104 _84465) (@lem3221103 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3221106 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term33 _84465 s P) = (term34 _84465 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3221105 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3221107 {_84465 : Type'} : (@GSPEC _84465) = (@GSPEC _84465).
Proof. exact (eq_refl (@GSPEC _84465)). Qed.
Lemma lem3221108 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term35 _84465 s P) = (term11 _84465 s P).
Proof. exact (MK_COMB (@lem3221107 _84465) (@lem3221106 _84465 s P)). Qed.
Lemma lem3221109 {_84465 : Type'} (x : _84465) : (@IN _84465 x) = (@IN _84465 x).
Proof. exact (eq_refl (@IN _84465 x)). Qed.
Lemma lem3221110 {_84465 : Type'} (x : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term21 _84465 x s P) = (term16 _84465 x s P).
Proof. exact (MK_COMB (@lem3221109 _84465 x) (@lem3221108 _84465 s P)). Qed.
Lemma lem3221111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3221112 {_84465 : Type'} (x : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term36 _84465 x s P) = (term37 _84465 x s P).
Proof. exact (MK_COMB (@lem3221111) (@lem3221110 _84465 x s P)). Qed.
Lemma lem3221113 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term22 _84465 s P x) = (term24 _84465 s P x).
Proof. exact (eq_refl (term22 _84465 s P x)). Qed.
Lemma lem3221114 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : ((term21 _84465 x s P) = (term22 _84465 s P x)) = ((term16 _84465 x s P) = (term24 _84465 s P x)).
Proof. exact (MK_COMB (@lem3221112 _84465 x s P) (@lem3221113 _84465 s P x)). Qed.
Lemma lem3221115 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term16 _84465 x s P) = (term24 _84465 s P x).
Proof. exact (EQ_MP (@lem3221114 _84465 s P x) (@lem3221097 _84465 s P x)). Qed.
Lemma lem3221118 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) (q' : Prop) : term38 _84465 s P x q'.
Proof. exact (@lem3221093 _84465 P x s (term24 _84465 s P x) q'). Qed.
Lemma lem3221119 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) (q' : Prop) : term39 _84465 s P x q'.
Proof. exact (@lem3221118 _84465 s P x q' (@lem3221115 _84465 s P x)). Qed.
Lemma lem3221120 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) (h1 : term24 _84465 s P x) : term24 _84465 s P x.
Proof. exact (h1). Qed.
Lemma lem3221124 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) (h1 : term24 _84465 s P x) : @IN _84465 x s.
Proof. exact (proj1 (@lem3221120 _84465 s P x h1)). Qed.
Lemma lem3221125 {_84465 : Type'} (x : _84465) (s : _84465 -> Prop) : (@IN _84465 x s) = ((@IN _84465 x s) = True).
Proof. exact (@lem7 (@IN _84465 x s)). Qed.
Lemma lem3221128 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) (h1 : term24 _84465 s P x) : (@IN _84465 x s) = True.
Proof. exact (EQ_MP (@lem3221125 _84465 x s) (@lem3221124 _84465 s P x h1)). Qed.
Lemma lem3221129 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) : term40 _84465 P x s.
Proof. exact (fun h0 : term24 _84465 s P x => @lem3221128 _84465 s P x h0). Qed.
Lemma lem3221130 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : term41 _84465 s P x.
Proof. exact (@lem3221119 _84465 s P x True). Qed.
Lemma lem3221131 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term42 _84465 P x s) = (term43 _84465 s P x).
Proof. exact (@lem3221130 _84465 s P x (@lem3221129 _84465 P x s)). Qed.
Lemma lem3221133 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3221134 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term43 _84465 s P x) = True.
Proof. exact (@lem3221133 (term24 _84465 s P x)). Qed.
Lemma lem3221135 {_84465 : Type'} (P : _84465 -> Prop) (x : _84465) (s : _84465 -> Prop) : (term42 _84465 P x s) = True.
Proof. exact (TRANS (@lem3221131 _84465 s P x) (@lem3221134 _84465 s P x)). Qed.
Lemma lem3221136 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term44 _84465 P s) = (term45 _84465).
Proof. exact (fun_ext (fun x : _84465 => @lem3221135 _84465 P x s)). Qed.
Lemma lem3221137 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3221138 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term10 _84465 P s) = (term46 _84465).
Proof. exact (MK_COMB (@lem3221137 _84465) (@lem3221136 _84465 P s)). Qed.
Lemma lem3221140 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3221141 {_84465 : Type'} (t : Prop) : (term47 _84465 t) = t.
Proof. exact (@lem3221140 _84465 t). Qed.
Lemma lem3221142 {_84465 : Type'} : (term46 _84465) = True.
Proof. exact (@lem3221141 _84465 True). Qed.
Lemma lem3221143 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term10 _84465 P s) = True.
Proof. exact (TRANS (@lem3221138 _84465 P s) (@lem3221142 _84465)). Qed.
Lemma lem3221144 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term9 _84465 P s) = True.
Proof. exact (TRANS (@lem3221076 _84465 P s) (@lem3221143 _84465 P s)). Qed.
Lemma lem3221145 {_84465 : Type'} (s : _84465 -> Prop) : (term48 _84465 s) = (term49 _84465).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3221144 _84465 P s)). Qed.
Lemma lem3221146 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3221147 {_84465 : Type'} (s : _84465 -> Prop) : (term50 _84465 s) = (term51 _84465).
Proof. exact (MK_COMB (@lem3221146 _84465) (@lem3221145 _84465 s)). Qed.
Lemma lem3221149 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3221150 {_84465 : Type'} (t : Prop) : (term52 _84465 t) = t.
Proof. exact (@lem3221149 (_84465 -> Prop) t). Qed.
Lemma lem3221151 {_84465 : Type'} : (term51 _84465) = True.
Proof. exact (@lem3221150 _84465 True). Qed.
Lemma lem3221152 {_84465 : Type'} (s : _84465 -> Prop) : (term50 _84465 s) = True.
Proof. exact (TRANS (@lem3221147 _84465 s) (@lem3221151 _84465)). Qed.
Lemma lem3221153 {_84465 : Type'} : (term53 _84465) = (term49 _84465).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3221152 _84465 s)). Qed.
Lemma lem3221154 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3221155 {_84465 : Type'} : (term54 _84465) = (term51 _84465).
Proof. exact (MK_COMB (@lem3221154 _84465) (@lem3221153 _84465)). Qed.
Lemma lem3221157 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3221158 {_84465 : Type'} (t : Prop) : (term52 _84465 t) = t.
Proof. exact (@lem3221157 (_84465 -> Prop) t). Qed.
Lemma lem3221159 {_84465 : Type'} : (term51 _84465) = True.
Proof. exact (@lem3221158 _84465 True). Qed.
Lemma lem3221160 {_84465 : Type'} : (term54 _84465) = True.
Proof. exact (TRANS (@lem3221155 _84465) (@lem3221159 _84465)). Qed.
Lemma lem3221161 {_84465 : Type'} : True = (term54 _84465).
Proof. exact (SYM (@lem3221160 _84465)). Qed.
Lemma lem3221162 {_84465 : Type'} : term54 _84465.
Proof. exact (EQ_MP (@lem3221161 _84465) (@lem0)). Qed.
