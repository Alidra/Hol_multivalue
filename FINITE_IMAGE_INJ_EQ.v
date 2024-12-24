Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_INJ_EQ_term_abbrevs.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_IMAGE_INJ_GENERAL_spec.
Require Import IMP_CONJ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1157_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm892_spec.
Lemma lem3617845 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (h1). Qed.
Lemma lem3617846 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3617847 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term0 a b) : a -> b.
Proof. exact (@lem3617845 a b h2 (@lem3617846 a b h1)). Qed.
Lemma lem3617848 (a : Prop) (b : Prop) (h1 : a = b) : term1 a b.
Proof. exact (fun h0 : term0 a b => @lem3617847 a b h1 h0). Qed.
Lemma lem3617849 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (h1). Qed.
Lemma lem3617850 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term0 a b) : a -> b.
Proof. exact (@lem3617848 a b h1 (@lem3617849 a b h2)). Qed.
Lemma lem3617851 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (fun h0 : a = b => @lem3617850 a b h0 h1). Qed.
Lemma lem3617852 (a : Prop) (b : Prop) : term2 a b.
Proof. exact (fun h0 : term0 a b => @lem3617851 a b h0). Qed.
Lemma lem3617854 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem3616275 A B f). Qed.
Lemma lem3617855 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem3617856 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem3617855 A B f) (@lem3617854 A B f)). Qed.
Lemma lem3617857 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term5 A B f A'.
Proof. exact (@lem3617856 A B f A'). Qed.
Lemma lem3617858 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term5 A B f A') = (term6 A B f A').
Proof. exact (eq_refl (term5 A B f A')). Qed.
Lemma lem3617859 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term6 A B f A'.
Proof. exact (EQ_MP (@lem3617858 A B f A') (@lem3617857 A B f A')). Qed.
Lemma lem3617860 {A B : Type'} (f : A -> B) (A' : B -> Prop) (s : A -> Prop) : term7 A B f A' s.
Proof. exact (@lem3617859 A B f A' s). Qed.
Lemma lem3617861 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term7 A B f A' s) = (term8 A B s f A').
Proof. exact (eq_refl (term7 A B f A' s)). Qed.
Lemma lem3617863 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term9 A B s f) : term9 A B s f.
Proof. exact (h1). Qed.
Lemma lem3618043 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3618044 {A B : Type'} (f : A -> B) : (term10 A B f) = (term11 A B f).
Proof. exact (eq_refl (term10 A B f)). Qed.
Lemma lem3618045 {A B : Type'} (f : A -> B) : term11 A B f.
Proof. exact (EQ_MP (@lem3618044 A B f) (@lem3618043 A B f)). Qed.
Lemma lem3618046 {A B : Type'} (f : A -> B) (s : A -> Prop) : term12 A B f s.
Proof. exact (@lem3618045 A B f s). Qed.
Lemma lem3618047 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term13 A B f s).
Proof. exact (eq_refl (term12 A B f s)). Qed.
Lemma lem3618048 {A B : Type'} (f : A -> B) (s : A -> Prop) : term13 A B f s.
Proof. exact (EQ_MP (@lem3618047 A B f s) (@lem3618046 A B f s)). Qed.
Lemma lem3618049 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3618050 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term14 A B f s.
Proof. exact (@lem3618048 A B f s (@lem3618049 A s h1)). Qed.
Lemma lem3618051 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term14 A B f s) = ((term14 A B f s) = True).
Proof. exact (@lem7 (term14 A B f s)). Qed.
Lemma lem3618052 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term14 A B f s) = True.
Proof. exact (EQ_MP (@lem3618051 A B f s) (@lem3618050 A B f s h1)). Qed.
Lemma lem3618078 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3618079 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem3618078 p q p' q'). Qed.
Lemma lem3618080 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem3618079 p q p'). Qed.
Lemma lem3618081 {A B : Type'} (f : A -> B) (s : A -> Prop) : term18 A B f s.
Proof. exact (@lem3618080 (@FINITE A s) (term14 A B f s)). Qed.
Lemma lem3618082 {A B : Type'} (f : A -> B) (s : A -> Prop) (p' : Prop) : term19 A B f s p'.
Proof. exact (@lem3618081 A B f s p'). Qed.
Lemma lem3618083 {A B : Type'} (f : A -> B) (s : A -> Prop) (p' : Prop) : (term19 A B f s p') = (term20 A B f s p').
Proof. exact (eq_refl (term19 A B f s p')). Qed.
Lemma lem3618084 {A B : Type'} (f : A -> B) (s : A -> Prop) (p' : Prop) : term20 A B f s p'.
Proof. exact (EQ_MP (@lem3618083 A B f s p') (@lem3618082 A B f s p')). Qed.
Lemma lem3618085 {A B : Type'} (f : A -> B) (s : A -> Prop) (p' : Prop) (q' : Prop) : term21 A B f s p' q'.
Proof. exact (@lem3618084 A B f s p' q'). Qed.
Lemma lem3618086 {A B : Type'} (f : A -> B) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term21 A B f s p' q') = (term22 A B f s p' q').
Proof. exact (eq_refl (term21 A B f s p' q')). Qed.
Lemma lem3618087 {A B : Type'} (f : A -> B) (s : A -> Prop) (p' : Prop) (q' : Prop) : term22 A B f s p' q'.
Proof. exact (EQ_MP (@lem3618086 A B f s p' q') (@lem3618085 A B f s p' q')). Qed.
Lemma lem3618100 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3618101 {A B : Type'} (f : A -> B) (s : A -> Prop) (q' : Prop) : term23 A B f s q'.
Proof. exact (@lem3618087 A B f s (@FINITE A s) q'). Qed.
Lemma lem3618102 {A B : Type'} (f : A -> B) (s : A -> Prop) (q' : Prop) : term24 A B f s q'.
Proof. exact (@lem3618101 A B f s q' (@lem3618100 A s)). Qed.
Lemma lem3618103 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3618104 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3618107 {A B : Type'} (f : A -> B) (s : A -> Prop) : term25 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3618052 A B f s h0). Qed.
Lemma lem3618108 {A B : Type'} (f : A -> B) (s : A -> Prop) : term25 A B f s.
Proof. exact (@lem3618107 A B f s). Qed.
Lemma lem3618110 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3618104 A s) (@lem3618103 A s h1)). Qed.
Lemma lem3618115 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3618110 A s h1)). Qed.
Lemma lem3618116 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3618115 A s h1) (@lem0)). Qed.
Lemma lem3618117 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term14 A B f s) = True.
Proof. exact (@lem3618108 A B f s (@lem3618116 A s h1)). Qed.
Lemma lem3618122 {A B : Type'} (f : A -> B) (s : A -> Prop) : term25 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3618117 A B f s h0). Qed.
Lemma lem3618123 {A B : Type'} (f : A -> B) (s : A -> Prop) : term26 A B f s.
Proof. exact (@lem3618102 A B f s True). Qed.
Lemma lem3618124 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term13 A B f s) = (term27 A s).
Proof. exact (@lem3618123 A B f s (@lem3618122 A B f s)). Qed.
Lemma lem3618126 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3618127 {A : Type'} (s : A -> Prop) : (term27 A s) = True.
Proof. exact (@lem3618126 (@FINITE A s)). Qed.
Lemma lem3618132 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term13 A B f s) = True.
Proof. exact (TRANS (@lem3618124 A B f s) (@lem3618127 A s)). Qed.
Lemma lem3618133 {A B : Type'} (f : A -> B) (s : A -> Prop) : True = (term13 A B f s).
Proof. exact (SYM (@lem3618132 A B f s)). Qed.
Lemma lem3618134 {A B : Type'} (f : A -> B) (s : A -> Prop) : term13 A B f s.
Proof. exact (EQ_MP (@lem3618133 A B f s) (@lem0)). Qed.
Lemma lem3618136 (p : Prop) (q : Prop) (r : Prop) : (term28 p q r) = (term29 p q r).
Proof. exact (EQ_MP (@lem892 p q r) (@lem887 p q r)). Qed.
Lemma lem3618137 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term30 A B f s) = (term31 A B f s).
Proof. exact (@lem3618136 (term9 A B s f) (term14 A B f s) (@FINITE A s)). Qed.
Lemma lem3618160 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term31 A B f s) = (term30 A B f s).
Proof. exact (SYM (@lem3618137 A B f s)). Qed.
Lemma lem3618161 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term32 A B f s) : term32 A B f s.
Proof. exact (h1). Qed.
Lemma lem3618163 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : term8 A B s f A'.
Proof. exact (EQ_MP (@lem3617861 A B s f A') (@lem3617860 A B f A' s)). Qed.
Lemma lem3618164 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : term8 A B s f A'.
Proof. exact (@lem3618163 A B s f A'). Qed.
Lemma lem3618165 {A B : Type'} (f : A -> B) (s : A -> Prop) : term33 A B f s.
Proof. exact (@lem3618164 A B s f (@IMAGE A B f s)). Qed.
Lemma lem3618166 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term32 A B f s) : term34 A B f s.
Proof. exact (@lem3618165 A B f s (@lem3618161 A B f s h1)). Qed.
Lemma lem3618168 (a : Prop) (b : Prop) : term0 a b.
Proof. exact (@lem3617852 a b (@lem1157 a b)). Qed.
Lemma lem3618169 {A B : Type'} (f : A -> B) (s : A -> Prop) : term35 A B f s.
Proof. exact (@lem3618168 (term34 A B f s) (@FINITE A s)). Qed.
Lemma lem3618170 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3618174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3618175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term36 A s t).
Proof. exact (@lem3618174 A s t). Qed.
Lemma lem3618176 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term37 A B f s) = s) = (term38 A B f s).
Proof. exact (@lem3618175 A (term37 A B f s) s). Qed.
Lemma lem3618191 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term38 A B f s) = ((term37 A B f s) = s).
Proof. exact (SYM (@lem3618176 A B f s)). Qed.
Lemma lem3618199 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term39 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3618200 {A : Type'} (p : A -> Prop) (x : A) : (term39 A x p) = (p x).
Proof. exact (@lem3618199 A p x). Qed.
Lemma lem3618201 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term40 A B x f s) = (term41 A B f s x).
Proof. exact (@lem3618200 A (term42 A B f s) x). Qed.
Lemma lem3618202 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term41 A B f s x) = (term43 A B x f s).
Proof. exact (eq_refl (term41 A B f s x)). Qed.
Lemma lem3618203 {A : Type'} (GEN_PVAR_95 : A) : (@SETSPEC A GEN_PVAR_95) = (@SETSPEC A GEN_PVAR_95).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_95)). Qed.
Lemma lem3618204 {A B : Type'} (GEN_PVAR_95 : A) (x : A) (f : A -> B) (s : A -> Prop) : (term44 A B GEN_PVAR_95 f s x) = (term45 A B GEN_PVAR_95 x f s).
Proof. exact (MK_COMB (@lem3618203 A GEN_PVAR_95) (@lem3618202 A B x f s)). Qed.
Lemma lem3618205 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3618206 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (s : A -> Prop) (x : A) : (term46 A B GEN_PVAR_95 f s x) = (term47 A B GEN_PVAR_95 f s x).
Proof. exact (MK_COMB (@lem3618204 A B GEN_PVAR_95 x f s) (@lem3618205 A x)). Qed.
Lemma lem3618207 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (s : A -> Prop) : (term48 A B GEN_PVAR_95 f s) = (term49 A B GEN_PVAR_95 f s).
Proof. exact (fun_ext (fun x : A => @lem3618206 A B GEN_PVAR_95 f s x)). Qed.
Lemma lem3618208 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618209 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (s : A -> Prop) : (term50 A B GEN_PVAR_95 f s) = (term51 A B GEN_PVAR_95 f s).
Proof. exact (MK_COMB (@lem3618208 A) (@lem3618207 A B GEN_PVAR_95 f s)). Qed.
Lemma lem3618210 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term52 A B f s) = (term53 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_95 : A => @lem3618209 A B GEN_PVAR_95 f s)). Qed.
Lemma lem3618211 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3618212 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term54 A B f s) = (term37 A B f s).
Proof. exact (MK_COMB (@lem3618211 A) (@lem3618210 A B f s)). Qed.
Lemma lem3618213 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3618214 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term40 A B x f s) = (term55 A B x f s).
Proof. exact (MK_COMB (@lem3618213 A x) (@lem3618212 A B f s)). Qed.
Lemma lem3618215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3618216 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term56 A B x f s) = (term57 A B x f s).
Proof. exact (MK_COMB (@lem3618215) (@lem3618214 A B x f s)). Qed.
Lemma lem3618217 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term41 A B f s x) = (term43 A B x f s).
Proof. exact (eq_refl (term41 A B f s x)). Qed.
Lemma lem3618218 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term40 A B x f s) = (term41 A B f s x)) = ((term55 A B x f s) = (term43 A B x f s)).
Proof. exact (MK_COMB (@lem3618216 A B x f s) (@lem3618217 A B x f s)). Qed.
Lemma lem3618219 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term55 A B x f s) = (term43 A B x f s).
Proof. exact (EQ_MP (@lem3618218 A B x f s) (@lem3618201 A B f s x)). Qed.
Lemma lem3618223 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3618224 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3618223 A P x). Qed.
Lemma lem3618225 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3618224 A s x). Qed.
Lemma lem3618226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618227 {A : Type'} (s : A -> Prop) (x : A) : (term58 A x s) = (term59 A s x).
Proof. exact (MK_COMB (@lem3618226) (@lem3618225 A s x)). Qed.
Lemma lem3618229 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term60 A B y f s) = (term61 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3618230 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term60 A B y f s) = (term61 A B y f s).
Proof. exact (@lem3618229 A B y f s). Qed.
Lemma lem3618231 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term62 A B x f s) = (term63 A B x f s).
Proof. exact (@lem3618230 A B (f x) f s). Qed.
Lemma lem3618241 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3618242 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3618241 A P x). Qed.
Lemma lem3618243 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3618242 A s x'). Qed.
Lemma lem3618244 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term64 A B x f x') = (term64 A B x f x').
Proof. exact (eq_refl (term64 A B x f x')). Qed.
Lemma lem3618245 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term65 A B x f x' s) = (term66 A B x f s x').
Proof. exact (MK_COMB (@lem3618244 A B x f x') (@lem3618243 A s x')). Qed.
Lemma lem3618248 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term67 A B x f s) = (term68 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618245 A B x f s x')). Qed.
Lemma lem3618249 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618250 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term63 A B x f s) = (term69 A B x f s).
Proof. exact (MK_COMB (@lem3618249 A) (@lem3618248 A B x f s)). Qed.
Lemma lem3618255 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term62 A B x f s) = (term69 A B x f s).
Proof. exact (TRANS (@lem3618231 A B x f s) (@lem3618250 A B x f s)). Qed.
Lemma lem3618256 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term43 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3618227 A s x) (@lem3618255 A B x f s)). Qed.
Lemma lem3618259 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term55 A B x f s) = (term70 A B x f s).
Proof. exact (TRANS (@lem3618219 A B x f s) (@lem3618256 A B x f s)). Qed.
Lemma lem3618260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3618261 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term57 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3618260) (@lem3618259 A B x f s)). Qed.
Lemma lem3618263 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3618264 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3618263 A P x). Qed.
Lemma lem3618265 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3618264 A s x). Qed.
Lemma lem3618266 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : ((term55 A B x f s) = (@IN A x s)) = ((term70 A B x f s) = (s x)).
Proof. exact (MK_COMB (@lem3618261 A B x f s) (@lem3618265 A s x)). Qed.
Lemma lem3618269 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term72 A B f s) = (term73 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3618266 A B f s x)). Qed.
Lemma lem3618270 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3618271 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term38 A B f s) = (term74 A B f s).
Proof. exact (MK_COMB (@lem3618270 A) (@lem3618269 A B f s)). Qed.
Lemma lem3618276 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term74 A B f s) = (term38 A B f s).
Proof. exact (SYM (@lem3618271 A B f s)). Qed.
Lemma lem3618278 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3618279 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term74 A B f s) = (term76 A B f s).
Proof. exact (@lem3618278 (term74 A B f s)). Qed.
Lemma lem3618280 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term76 A B f s) = (term74 A B f s).
Proof. exact (SYM (@lem3618279 A B f s)). Qed.
Lemma lem3618281 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term77 A B f s) : term77 A B f s.
Proof. exact (h1). Qed.
Lemma lem3618284 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term76 A B f s) : term76 A B f s.
Proof. exact (h1). Qed.
Lemma lem3618285 {A B : Type'} (f : A -> B) (s : A -> Prop) : term78 A B f s.
Proof. exact (fun h0 : term76 A B f s => @lem3618284 A B f s h0). Qed.
Lemma lem3618286 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term78 A B f s) : term78 A B f s.
Proof. exact (h1). Qed.
Lemma lem3618287 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term76 A B f s) : term76 A B f s.
Proof. exact (h1). Qed.
Lemma lem3618288 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term76 A B f s) (h2 : term78 A B f s) : term76 A B f s.
Proof. exact (@lem3618286 A B f s h2 (@lem3618287 A B f s h1)). Qed.
Lemma lem3618289 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term76 A B f s) : term79 A B f s.
Proof. exact (fun h0 : term78 A B f s => @lem3618288 A B f s h1 h0). Qed.
Lemma lem3618290 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term78 A B f s) : term78 A B f s.
Proof. exact (h1). Qed.
Lemma lem3618291 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term76 A B f s) (h2 : term78 A B f s) : term76 A B f s.
Proof. exact (@lem3618289 A B f s h1 (@lem3618290 A B f s h2)). Qed.
Lemma lem3618292 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term78 A B f s) : term78 A B f s.
Proof. exact (fun h0 : term76 A B f s => @lem3618291 A B f s h0 h1). Qed.
Lemma lem3618293 {A B : Type'} (f : A -> B) (s : A -> Prop) : term80 A B f s.
Proof. exact (fun h0 : term78 A B f s => @lem3618292 A B f s h0). Qed.
Lemma lem3618296 {A B : Type'} (f : A -> B) (s : A -> Prop) : term78 A B f s.
Proof. exact (@lem3618293 A B f s (@lem3618285 A B f s)). Qed.
Lemma lem3618297 {A B : Type'} (f : A -> B) (s : A -> Prop) : term78 A B f s.
Proof. exact (@lem3618296 A B f s). Qed.
Lemma lem3618307 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3618308 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term76 A B f s) = (term81 A B f s).
Proof. exact (@lem3618307 (term77 A B f s)). Qed.
Lemma lem3618310 (t : Prop) : (term82 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3618311 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term81 A B f s) = (term74 A B f s).
Proof. exact (@lem3618310 (term74 A B f s)). Qed.
Lemma lem3618316 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term76 A B f s) = (term74 A B f s).
Proof. exact (TRANS (@lem3618308 A B f s) (@lem3618311 A B f s)). Qed.
Lemma lem3618353 {A B : Type'} (s : A -> Prop) : (term83 A B s) = (term84 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3618316 A B f s)). Qed.
Lemma lem3618354 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3618355 {A B : Type'} (s : A -> Prop) : (term85 A B s) = (term86 A B s).
Proof. exact (MK_COMB (@lem3618354 A B) (@lem3618353 A B s)). Qed.
Lemma lem3618360 {A B : Type'} : (term87 A B) = (term88 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3618355 A B s)). Qed.
Lemma lem3618361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3618370 {A B : Type'} : (term89 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem3618361 A) (@lem3618360 A B)). Qed.
Lemma lem3618371 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3618376 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term66 A B x f s x') = (term66 A B x f s x').
Proof. exact (eq_refl (term66 A B x f s x')). Qed.
Lemma lem3618377 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term68 A B x f s) = (term68 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618376 A B x f s x')). Qed.
Lemma lem3618378 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618379 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term69 A B x f s) = (term69 A B x f s).
Proof. exact (MK_COMB (@lem3618378 A) (@lem3618377 A B x f s)). Qed.
Lemma lem3618382 {A : Type'} (s : A -> Prop) (x : A) : (term59 A s x) = (term59 A s x).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem3618383 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3618382 A s x) (@lem3618379 A B x f s)). Qed.
Lemma lem3618384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3618385 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3618384) (@lem3618383 A B x f s)). Qed.
Lemma lem3618386 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : ((term70 A B x f s) = (s x)) = ((term70 A B x f s) = (s x)).
Proof. exact (MK_COMB (@lem3618385 A B x f s) (@lem3618371 A s x)). Qed.
Lemma lem3618387 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term73 A B f s) = (term73 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3618386 A B f s x)). Qed.
Lemma lem3618388 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3618389 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term74 A B f s) = (term74 A B f s).
Proof. exact (MK_COMB (@lem3618388 A) (@lem3618387 A B f s)). Qed.
Lemma lem3618390 {A B : Type'} (s : A -> Prop) : (term84 A B s) = (term84 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3618389 A B f s)). Qed.
Lemma lem3618391 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3618392 {A B : Type'} (s : A -> Prop) : (term86 A B s) = (term86 A B s).
Proof. exact (MK_COMB (@lem3618391 A B) (@lem3618390 A B s)). Qed.
Lemma lem3618393 {A B : Type'} : (term88 A B) = (term88 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3618392 A B s)). Qed.
Lemma lem3618394 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3618395 {A B : Type'} : (term90 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem3618394 A) (@lem3618393 A B)). Qed.
Lemma lem3618426 {A B : Type'} : (term89 A B) = (term90 A B).
Proof. exact (TRANS (@lem3618370 A B) (@lem3618395 A B)). Qed.
Lemma lem3618427 {A B : Type'} : (term90 A B) = (term89 A B).
Proof. exact (SYM (@lem3618426 A B)). Qed.
Lemma lem3618429 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3618430 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : ((term70 A B x f s) = (s x)) = (term91 A B f s x).
Proof. exact (@lem3618429 ((term70 A B x f s) = (s x))). Qed.
Lemma lem3618431 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term91 A B f s x) = ((term70 A B x f s) = (s x)).
Proof. exact (SYM (@lem3618430 A B f s x)). Qed.
Lemma lem3618432 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term92 A B f s x) : term92 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3618443 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term93 A B x f s x') = (term94 A B x f s x').
Proof. exact (@lem17045 ((f x) = (f x')) (s x')). Qed.
Lemma lem3618446 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term66 A B x f s x') = (term66 A B x f s x').
Proof. exact (eq_refl (term66 A B x f s x')). Qed.
Lemma lem3618447 {A : Type'} (P : A -> Prop) : (term95 A P) = (term96 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3618448 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term97 A B x f s) = (term98 A B x f s).
Proof. exact (@lem3618447 A (term68 A B x f s)). Qed.
Lemma lem3618449 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term99 A B x f s x') = (term66 A B x f s x').
Proof. exact (eq_refl (term99 A B x f s x')). Qed.
Lemma lem3618450 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3618451 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term100 A B x f s x') = (term93 A B x f s x').
Proof. exact (MK_COMB (@lem3618450) (@lem3618449 A B x f s x')). Qed.
Lemma lem3618452 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term100 A B x f s x') = (term94 A B x f s x').
Proof. exact (TRANS (@lem3618451 A B x f s x') (@lem3618443 A B x f s x')). Qed.
Lemma lem3618453 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term101 A B x f s) = (term102 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618452 A B x f s x')). Qed.
Lemma lem3618454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3618455 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term98 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem3618454 A) (@lem3618453 A B x f s)). Qed.
Lemma lem3618456 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term97 A B x f s) = (term103 A B x f s).
Proof. exact (TRANS (@lem3618448 A B x f s) (@lem3618455 A B x f s)). Qed.
Lemma lem3618457 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term68 A B x f s) = (term68 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618446 A B x f s x')). Qed.
Lemma lem3618458 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618459 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term69 A B x f s) = (term69 A B x f s).
Proof. exact (MK_COMB (@lem3618458 A) (@lem3618457 A B x f s)). Qed.
Lemma lem3618461 {A : Type'} (s : A -> Prop) (x : A) : (term104 A s x) = (term104 A s x).
Proof. exact (eq_refl (term104 A s x)). Qed.
Lemma lem3618462 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term105 A B x f s) = (term106 A B x f s).
Proof. exact (MK_COMB (@lem3618461 A s x) (@lem3618456 A B x f s)). Qed.
Lemma lem3618463 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term107 A B x f s) = (term105 A B x f s).
Proof. exact (@lem17045 (s x) (term69 A B x f s)). Qed.
Lemma lem3618464 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term107 A B x f s) = (term106 A B x f s).
Proof. exact (TRANS (@lem3618463 A B x f s) (@lem3618462 A B x f s)). Qed.
Lemma lem3618466 {A : Type'} (s : A -> Prop) (x : A) : (term59 A s x) = (term59 A s x).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem3618467 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3618466 A s x) (@lem3618459 A B x f s)). Qed.
Lemma lem3618468 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3618469 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3618470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618471 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term109 A B x f s) = (term110 A B x f s).
Proof. exact (MK_COMB (@lem3618470) (@lem3618464 A B x f s)). Qed.
Lemma lem3618472 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term111 A B f s x) = (term112 A B f s x).
Proof. exact (MK_COMB (@lem3618471 A B x f s) (@lem3618469 A s x)). Qed.
Lemma lem3618473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618474 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term113 A B x f s) = (term113 A B x f s).
Proof. exact (MK_COMB (@lem3618473) (@lem3618467 A B x f s)). Qed.
Lemma lem3618475 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term114 A B f s x) = (term114 A B f s x).
Proof. exact (MK_COMB (@lem3618474 A B x f s) (@lem3618468 A s x)). Qed.
Lemma lem3618476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3618477 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term115 A B f s x) = (term115 A B f s x).
Proof. exact (MK_COMB (@lem3618476) (@lem3618475 A B f s x)). Qed.
Lemma lem3618478 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term116 A B f s x) = (term117 A B f s x).
Proof. exact (MK_COMB (@lem3618477 A B f s x) (@lem3618472 A B f s x)). Qed.
Lemma lem3618479 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term92 A B f s x) = (term116 A B f s x).
Proof. exact (@lem17646 (term70 A B x f s) (s x)). Qed.
Lemma lem3618480 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term92 A B f s x) = (term117 A B f s x).
Proof. exact (TRANS (@lem3618479 A B f s x) (@lem3618478 A B f s x)). Qed.
Lemma lem3618563 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3618564 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (@lem3618563 A P Q). Qed.
Lemma lem3618565 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term121 A B x f s).
Proof. exact (@lem3618564 A (s x) (term68 A B x f s)). Qed.
Lemma lem3618566 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term99 A B x f s x') = (term66 A B x f s x').
Proof. exact (eq_refl (term99 A B x f s x')). Qed.
Lemma lem3618567 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term122 A B x f s) = (term68 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618566 A B x f s x')). Qed.
Lemma lem3618568 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618569 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term123 A B x f s) = (term69 A B x f s).
Proof. exact (MK_COMB (@lem3618568 A) (@lem3618567 A B x f s)). Qed.
Lemma lem3618570 {A : Type'} (s : A -> Prop) (x : A) : (term59 A s x) = (term59 A s x).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem3618571 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3618570 A s x) (@lem3618569 A B x f s)). Qed.
Lemma lem3618572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3618573 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term124 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3618572) (@lem3618571 A B x f s)). Qed.
Lemma lem3618574 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term99 A B x f s x') = (term66 A B x f s x').
Proof. exact (eq_refl (term99 A B x f s x')). Qed.
Lemma lem3618575 {A : Type'} (s : A -> Prop) (x : A) : (term59 A s x) = (term59 A s x).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem3618576 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term125 A B x f s x') = (term126 A B x f s x').
Proof. exact (MK_COMB (@lem3618575 A s x) (@lem3618574 A B x f s x')). Qed.
Lemma lem3618577 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term128 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618576 A B x f s x')). Qed.
Lemma lem3618578 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618579 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term121 A B x f s) = (term129 A B x f s).
Proof. exact (MK_COMB (@lem3618578 A) (@lem3618577 A B x f s)). Qed.
Lemma lem3618580 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term120 A B x f s) = (term121 A B x f s)) = ((term70 A B x f s) = (term129 A B x f s)).
Proof. exact (MK_COMB (@lem3618573 A B x f s) (@lem3618579 A B x f s)). Qed.
Lemma lem3618581 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term129 A B x f s).
Proof. exact (EQ_MP (@lem3618580 A B x f s) (@lem3618565 A B x f s)). Qed.
Lemma lem3618582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618583 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term113 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem3618582) (@lem3618581 A B x f s)). Qed.
Lemma lem3618584 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3618585 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term114 A B f s x) = (term131 A B f s x).
Proof. exact (MK_COMB (@lem3618583 A B x f s) (@lem3618584 A s x)). Qed.
Lemma lem3618587 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3618588 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (@lem3618587 A P Q). Qed.
Lemma lem3618589 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term134 A B f s x) = (term135 A B f s x).
Proof. exact (@lem3618588 A (term128 A B x f s) (term108 A s x)). Qed.
Lemma lem3618590 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term136 A B x f s x') = (term126 A B x f s x').
Proof. exact (eq_refl (term136 A B x f s x')). Qed.
Lemma lem3618591 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term137 A B x f s) = (term128 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618590 A B x f s x')). Qed.
Lemma lem3618592 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618593 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term138 A B x f s) = (term129 A B x f s).
Proof. exact (MK_COMB (@lem3618592 A) (@lem3618591 A B x f s)). Qed.
Lemma lem3618594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618595 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term139 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem3618594) (@lem3618593 A B x f s)). Qed.
Lemma lem3618596 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3618597 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term134 A B f s x) = (term131 A B f s x).
Proof. exact (MK_COMB (@lem3618595 A B x f s) (@lem3618596 A s x)). Qed.
Lemma lem3618598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3618599 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term140 A B f s x) = (term141 A B f s x).
Proof. exact (MK_COMB (@lem3618598) (@lem3618597 A B f s x)). Qed.
Lemma lem3618600 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term136 A B x f s x') = (term126 A B x f s x').
Proof. exact (eq_refl (term136 A B x f s x')). Qed.
Lemma lem3618601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618602 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term142 A B x f s x') = (term143 A B x f s x').
Proof. exact (MK_COMB (@lem3618601) (@lem3618600 A B x f s x')). Qed.
Lemma lem3618603 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3618604 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term144 A B f x' s x) = (term145 A B f x' s x).
Proof. exact (MK_COMB (@lem3618602 A B x f s x') (@lem3618603 A s x)). Qed.
Lemma lem3618605 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term146 A B f s x) = (term147 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3618604 A B f x' s x)). Qed.
Lemma lem3618606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618607 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term135 A B f s x) = (term148 A B f s x).
Proof. exact (MK_COMB (@lem3618606 A) (@lem3618605 A B f s x)). Qed.
Lemma lem3618608 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : ((term134 A B f s x) = (term135 A B f s x)) = ((term131 A B f s x) = (term148 A B f s x)).
Proof. exact (MK_COMB (@lem3618599 A B f s x) (@lem3618607 A B f s x)). Qed.
Lemma lem3618609 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term131 A B f s x) = (term148 A B f s x).
Proof. exact (EQ_MP (@lem3618608 A B f s x) (@lem3618589 A B f s x)). Qed.
Lemma lem3618610 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term114 A B f s x) = (term148 A B f s x).
Proof. exact (TRANS (@lem3618585 A B f s x) (@lem3618609 A B f s x)). Qed.
Lemma lem3618611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3618612 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term115 A B f s x) = (term149 A B f s x).
Proof. exact (MK_COMB (@lem3618611) (@lem3618610 A B f s x)). Qed.
Lemma lem3618613 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term112 A B f s x) = (term112 A B f s x).
Proof. exact (eq_refl (term112 A B f s x)). Qed.
Lemma lem3618614 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term117 A B f s x) = (term150 A B f s x).
Proof. exact (MK_COMB (@lem3618612 A B f s x) (@lem3618613 A B f s x)). Qed.
Lemma lem3618616 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3618617 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem3618616 A P Q). Qed.
Lemma lem3618618 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term153 A B f s x) = (term154 A B f s x).
Proof. exact (@lem3618617 A (term147 A B f s x) (term112 A B f s x)). Qed.
Lemma lem3618619 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term155 A B f s x x') = (term145 A B f x' s x).
Proof. exact (eq_refl (term155 A B f s x x')). Qed.
Lemma lem3618620 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term156 A B f s x) = (term147 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3618619 A B f x' s x)). Qed.
Lemma lem3618621 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618622 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term157 A B f s x) = (term148 A B f s x).
Proof. exact (MK_COMB (@lem3618621 A) (@lem3618620 A B f s x)). Qed.
Lemma lem3618623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3618624 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term158 A B f s x) = (term149 A B f s x).
Proof. exact (MK_COMB (@lem3618623) (@lem3618622 A B f s x)). Qed.
Lemma lem3618625 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term112 A B f s x) = (term112 A B f s x).
Proof. exact (eq_refl (term112 A B f s x)). Qed.
Lemma lem3618626 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term153 A B f s x) = (term150 A B f s x).
Proof. exact (MK_COMB (@lem3618624 A B f s x) (@lem3618625 A B f s x)). Qed.
Lemma lem3618627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3618628 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term159 A B f s x) = (term160 A B f s x).
Proof. exact (MK_COMB (@lem3618627) (@lem3618626 A B f s x)). Qed.
Lemma lem3618629 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term155 A B f s x x') = (term145 A B f x' s x).
Proof. exact (eq_refl (term155 A B f s x x')). Qed.
Lemma lem3618630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3618631 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term161 A B f s x x') = (term162 A B f x' s x).
Proof. exact (MK_COMB (@lem3618630) (@lem3618629 A B f x' s x)). Qed.
Lemma lem3618632 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term112 A B f s x) = (term112 A B f s x).
Proof. exact (eq_refl (term112 A B f s x)). Qed.
Lemma lem3618633 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) : (term163 A B x' f s x) = (term164 A B x' f s x).
Proof. exact (MK_COMB (@lem3618631 A B f x' s x) (@lem3618632 A B f s x)). Qed.
Lemma lem3618634 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term165 A B f s x) = (term166 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3618633 A B x' f s x)). Qed.
Lemma lem3618635 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3618636 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term154 A B f s x) = (term167 A B f s x).
Proof. exact (MK_COMB (@lem3618635 A) (@lem3618634 A B f s x)). Qed.
Lemma lem3618637 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : ((term153 A B f s x) = (term154 A B f s x)) = ((term150 A B f s x) = (term167 A B f s x)).
Proof. exact (MK_COMB (@lem3618628 A B f s x) (@lem3618636 A B f s x)). Qed.
Lemma lem3618638 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term150 A B f s x) = (term167 A B f s x).
Proof. exact (EQ_MP (@lem3618637 A B f s x) (@lem3618618 A B f s x)). Qed.
Lemma lem3618640 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term117 A B f s x) = (term167 A B f s x).
Proof. exact (TRANS (@lem3618614 A B f s x) (@lem3618638 A B f s x)). Qed.
Lemma lem3618641 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term92 A B f s x) = (term167 A B f s x).
Proof. exact (TRANS (@lem3618480 A B f s x) (@lem3618640 A B f s x)). Qed.
Lemma lem3618642 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term92 A B f s x) : term167 A B f s x.
Proof. exact (EQ_MP (@lem3618641 A B f s x) (@lem3618432 A B f s x h1)). Qed.
Lemma lem3618643 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term164 A B x' f s x) : term164 A B x' f s x.
Proof. exact (h1). Qed.
Lemma lem3618646 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3618665 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term94 A B x f s x') = (term94 A B x f s x').
Proof. exact (eq_refl (term94 A B x f s x')). Qed.
Lemma lem3618666 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term102 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618665 A B x f s x')). Qed.
Lemma lem3618667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3618668 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem3618667 A) (@lem3618666 A B x f s)). Qed.
Lemma lem3618675 {A : Type'} (s : A -> Prop) (x : A) : (term104 A s x) = (term104 A s x).
Proof. exact (eq_refl (term104 A s x)). Qed.
Lemma lem3618676 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term106 A B x f s) = (term106 A B x f s).
Proof. exact (MK_COMB (@lem3618675 A s x) (@lem3618668 A B x f s)). Qed.
Lemma lem3618677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3618678 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term110 A B x f s) = (term110 A B x f s).
Proof. exact (MK_COMB (@lem3618677) (@lem3618676 A B x f s)). Qed.
Lemma lem3618679 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term112 A B f s x) = (term112 A B f s x).
Proof. exact (MK_COMB (@lem3618678 A B x f s) (@lem3618646 A s x)). Qed.
Lemma lem3618710 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term162 A B f x' s x) = (term162 A B f x' s x).
Proof. exact (eq_refl (term162 A B f x' s x)). Qed.
Lemma lem3618711 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) : (term164 A B x' f s x) = (term164 A B x' f s x).
Proof. exact (MK_COMB (@lem3618710 A B f x' s x) (@lem3618679 A B f s x)). Qed.
Lemma lem3618712 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term164 A B x' f s x) : term164 A B x' f s x.
Proof. exact (EQ_MP (@lem3618711 A B x' f s x) (@lem3618643 A B x' f s x h1)). Qed.
Lemma lem3618713 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : term145 A B f x' s x.
Proof. exact (h1). Qed.
Lemma lem3618714 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : term112 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3618716 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : term126 A B x f s x'.
Proof. exact (proj1 (@lem3618713 A B f x' s x h1)). Qed.
Lemma lem3618722 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : term106 A B x f s.
Proof. exact (proj1 (@lem3618714 A B f s x h1)). Qed.
Lemma lem3618724 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term103 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3618748 {A : Type'} (s : A -> Prop) (x : A) (h1 : term108 A s x) : term108 A s x.
Proof. exact (h1). Qed.
Lemma lem3618760 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term94 A B x f s x') = (term94 A B x f s x').
Proof. exact (eq_refl (term94 A B x f s x')). Qed.
Lemma lem3618761 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term102 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3618760 A B x f s x')). Qed.
Lemma lem3618762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3618764 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem3618762 A) (@lem3618761 A B x f s)). Qed.
Lemma lem3618765 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term103 A B x f s.
Proof. exact (EQ_MP (@lem3618764 A B x f s) (@lem3618724 A B x f s h1)). Qed.
Lemma lem3618766 {A B : Type'} (_39313 : A) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term168 A B x f s _39313.
Proof. exact (@lem3618765 A B x f s h1 _39313). Qed.
Lemma lem3618767 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_39313 : A) : (term168 A B x f s _39313) = (term94 A B x f s _39313).
Proof. exact (eq_refl (term168 A B x f s _39313)). Qed.
Lemma lem3618770 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : term108 A s x.
Proof. exact (proj2 (@lem3618713 A B f x' s x h1)). Qed.
Lemma lem3618780 {A : Type'} (s : A -> Prop) (x : A) (h1 : term108 A s x) : term108 A s x.
Proof. exact (h1). Qed.
Lemma lem3618788 {A B : Type'} (_39313 : A) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term94 A B x f s _39313.
Proof. exact (EQ_MP (@lem3618767 A B x f s _39313) (@lem3618766 A B _39313 x f s h1)). Qed.
Lemma lem3618814 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : s x.
Proof. exact (proj1 (@lem3618716 A B f x' s x h1)). Qed.
Lemma lem3618815 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : term169 A s x.
Proof. exact (fun h0 : term108 A s x => @lem3618814 A B f x' s x h1). Qed.
Lemma lem3618817 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618818 {A : Type'} (s : A -> Prop) (x : A) : (term169 A s x) = (s x).
Proof. exact (@lem3618817 (s x)). Qed.
Lemma lem3618819 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : s x.
Proof. exact (EQ_MP (@lem3618818 A s x) (@lem3618815 A B f x' s x h1)). Qed.
Lemma lem3618822 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3618824 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term171 A s x).
Proof. exact (@lem3618822 (s x)). Qed.
Lemma lem3618827 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : term171 A s x.
Proof. exact (EQ_MP (@lem3618824 A s x) (@lem3618770 A B f x' s x h1)). Qed.
Lemma lem3618830 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : False.
Proof. exact (@lem3618827 A B f x' s x h1 (@lem3618819 A B f x' s x h1)). Qed.
Lemma lem3618831 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : term172.
Proof. exact (fun h0 : ~ False => @lem3618830 A B f x' s x h1). Qed.
Lemma lem3618833 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618834 : term172 = False.
Proof. exact (@lem3618833 False). Qed.
Lemma lem3618835 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) (h1 : term145 A B f x' s x) : False.
Proof. exact (EQ_MP (@lem3618834) (@lem3618831 A B f x' s x h1)). Qed.
Lemma lem3618837 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : s x.
Proof. exact (proj2 (@lem3618714 A B f s x h1)). Qed.
Lemma lem3618838 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : term169 A s x.
Proof. exact (fun h0 : term108 A s x => @lem3618837 A B f s x h1). Qed.
Lemma lem3618840 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618841 {A : Type'} (s : A -> Prop) (x : A) : (term169 A s x) = (s x).
Proof. exact (@lem3618840 (s x)). Qed.
Lemma lem3618842 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : s x.
Proof. exact (EQ_MP (@lem3618841 A s x) (@lem3618838 A B f s x h1)). Qed.
Lemma lem3618845 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3618847 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term171 A s x).
Proof. exact (@lem3618845 (s x)). Qed.
Lemma lem3618850 {A : Type'} (s : A -> Prop) (x : A) (h1 : term108 A s x) : term171 A s x.
Proof. exact (EQ_MP (@lem3618847 A s x) (@lem3618780 A s x h1)). Qed.
Lemma lem3618853 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : False.
Proof. exact (@lem3618850 A s x h1 (@lem3618842 A B f s x h2)). Qed.
Lemma lem3618854 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : term172.
Proof. exact (fun h0 : ~ False => @lem3618853 A B f s x h1 h2). Qed.
Lemma lem3618856 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618857 : term172 = False.
Proof. exact (@lem3618856 False). Qed.
Lemma lem3618858 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618857) (@lem3618854 A B f s x h1 h2)). Qed.
Lemma lem3618884 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3618885 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3618884 B x). Qed.
Lemma lem3618886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3618885 B (f x)). Qed.
Lemma lem3618887 {A B : Type'} (f : A -> B) (x : A) : term173 A B f x.
Proof. exact (fun h0 : term174 A B f x => @lem3618886 A B f x). Qed.
Lemma lem3618889 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618890 {A B : Type'} (f : A -> B) (x : A) : (term173 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3618889 ((f x) = (f x))). Qed.
Lemma lem3618891 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3618890 A B f x) (@lem3618887 A B f x)). Qed.
Lemma lem3618893 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : s x.
Proof. exact (proj2 (@lem3618714 A B f s x h1)). Qed.
Lemma lem3618894 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : term169 A s x.
Proof. exact (fun h0 : term108 A s x => @lem3618893 A B f s x h1). Qed.
Lemma lem3618896 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618897 {A : Type'} (s : A -> Prop) (x : A) : (term169 A s x) = (s x).
Proof. exact (@lem3618896 (s x)). Qed.
Lemma lem3618898 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : s x.
Proof. exact (EQ_MP (@lem3618897 A s x) (@lem3618894 A B f s x h1)). Qed.
Lemma lem3618900 (a : Prop) (b : Prop) : (term175 a b) = (term176 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3618901 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_39313 : A) : (term94 A B x f s _39313) = (term93 A B x f s _39313).
Proof. exact (@lem3618900 ((f x) = (f _39313)) (s _39313)). Qed.
Lemma lem3618903 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3618904 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_39313 : A) : (term93 A B x f s _39313) = (term177 A B x f s _39313).
Proof. exact (@lem3618903 (term66 A B x f s _39313)). Qed.
Lemma lem3618905 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_39313 : A) : (term94 A B x f s _39313) = (term177 A B x f s _39313).
Proof. exact (TRANS (@lem3618901 A B x f s _39313) (@lem3618904 A B x f s _39313)). Qed.
Lemma lem3618907 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : term178 A B f s x.
Proof. exact (conj (@lem3618891 A B f x) (@lem3618898 A B f s x h1)). Qed.
Lemma lem3618909 {A B : Type'} (_39313 : A) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term177 A B x f s _39313.
Proof. exact (EQ_MP (@lem3618905 A B x f s _39313) (@lem3618788 A B _39313 x f s h1)). Qed.
Lemma lem3618910 {A B : Type'} (_39313 : A) (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term177 A B x f s _39313.
Proof. exact (@lem3618909 A B _39313 x f s h1). Qed.
Lemma lem3618911 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x f s) : term179 A B f s x.
Proof. exact (@lem3618910 A B x x f s h1). Qed.
Lemma lem3618914 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term103 A B x f s) (h2 : term112 A B f s x) : False.
Proof. exact (@lem3618911 A B x f s h1 (@lem3618907 A B f s x h2)). Qed.
Lemma lem3618915 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term103 A B x f s) (h2 : term112 A B f s x) : term172.
Proof. exact (fun h0 : ~ False => @lem3618914 A B f s x h1 h2). Qed.
Lemma lem3618917 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3618918 : term172 = False.
Proof. exact (@lem3618917 False). Qed.
Lemma lem3618919 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term103 A B x f s) (h2 : term112 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618918) (@lem3618915 A B f s x h1 h2)). Qed.
Lemma lem3618920 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : (term108 A s x) = False.
Proof. exact (prop_ext (fun h3 : term108 A s x => @lem3618858 A B f s x h1 h2) (fun h3 : False => @lem3618780 A s x h1)). Qed.
Lemma lem3618921 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618920 A B f s x h1 h2) (@lem3618780 A s x h1)). Qed.
Lemma lem3618922 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : (term108 A s x) = False.
Proof. exact (prop_ext (fun h3 : term108 A s x => @lem3618921 A B f s x h1 h2) (fun h3 : False => @lem3618748 A s x h1)). Qed.
Lemma lem3618923 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618922 A B f s x h1 h2) (@lem3618748 A s x h1)). Qed.
Lemma lem3618924 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term103 A B x f s) (h2 : term112 A B f s x) : (term103 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term103 A B x f s => @lem3618919 A B f s x h1 h2) (fun h3 : False => @lem3618765 A B x f s h1)). Qed.
Lemma lem3618925 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term103 A B x f s) (h2 : term112 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618924 A B f s x h1 h2) (@lem3618765 A B x f s h1)). Qed.
Lemma lem3618926 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : (term108 A s x) = False.
Proof. exact (prop_ext (fun h3 : term108 A s x => @lem3618923 A B f s x h1 h2) (fun h3 : False => @lem3618748 A s x h1)). Qed.
Lemma lem3618927 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term108 A s x) (h2 : term112 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618926 A B f s x h1 h2) (@lem3618748 A s x h1)). Qed.
Lemma lem3618928 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term112 A B f s x) : False.
Proof. exact (or_elim (@lem3618722 A B f s x h1) (fun h0 : term108 A s x => @lem3618927 A B f s x h0 h1) (fun h0 : term103 A B x f s => @lem3618925 A B f s x h0 h1)). Qed.
Lemma lem3618929 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term164 A B x' f s x) : False.
Proof. exact (or_elim (@lem3618712 A B x' f s x h1) (fun h0 : term145 A B f x' s x => @lem3618835 A B f x' s x h0) (fun h0 : term112 A B f s x => @lem3618928 A B f s x h0)). Qed.
Lemma lem3618930 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term164 A B x' f s x) : (term164 A B x' f s x) = False.
Proof. exact (prop_ext (fun h2 : term164 A B x' f s x => @lem3618929 A B x' f s x h1) (fun h2 : False => @lem3618712 A B x' f s x h1)). Qed.
Lemma lem3618931 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term164 A B x' f s x) : False.
Proof. exact (EQ_MP (@lem3618930 A B x' f s x h1) (@lem3618712 A B x' f s x h1)). Qed.
Lemma lem3618932 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term92 A B f s x) : False.
Proof. exact (ex_elim (@lem3618642 A B f s x h1) (fun x' : A => fun h0 : term166 A B f s x x' => @lem3618931 A B x' f s x h0)). Qed.
Lemma lem3618933 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term92 A B f s x) : (term92 A B f s x) = False.
Proof. exact (prop_ext (fun h2 : term92 A B f s x => @lem3618932 A B f s x h1) (fun h2 : False => @lem3618432 A B f s x h1)). Qed.
Lemma lem3618934 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : term92 A B f s x) : False.
Proof. exact (EQ_MP (@lem3618933 A B f s x h1) (@lem3618432 A B f s x h1)). Qed.
Lemma lem3618935 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : term91 A B f s x.
Proof. exact (fun h0 : term92 A B f s x => @lem3618934 A B f s x h0). Qed.
Lemma lem3618936 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term70 A B x f s) = (s x).
Proof. exact (EQ_MP (@lem3618431 A B f s x) (@lem3618935 A B f s x)). Qed.
Lemma lem3618941 {A B : Type'} (f : A -> B) (s : A -> Prop) : term74 A B f s.
Proof. exact (fun x : A => @lem3618936 A B f s x). Qed.
Lemma lem3618946 {A B : Type'} (s : A -> Prop) : term86 A B s.
Proof. exact (fun f : A -> B => @lem3618941 A B f s). Qed.
Lemma lem3618951 {A B : Type'} : term90 A B.
Proof. exact (fun s : A -> Prop => @lem3618946 A B s). Qed.
Lemma lem3618952 {A B : Type'} : term89 A B.
Proof. exact (EQ_MP (@lem3618427 A B) (@lem3618951 A B)). Qed.
Lemma lem3618953 {A B : Type'} (s : A -> Prop) : term180 A B s.
Proof. exact (@lem3618952 A B s). Qed.
Lemma lem3618954 {A B : Type'} (s : A -> Prop) : (term180 A B s) = (term85 A B s).
Proof. exact (eq_refl (term180 A B s)). Qed.
Lemma lem3618955 {A B : Type'} (s : A -> Prop) : term85 A B s.
Proof. exact (EQ_MP (@lem3618954 A B s) (@lem3618953 A B s)). Qed.
Lemma lem3618956 {A B : Type'} (s : A -> Prop) (f : A -> B) : term181 A B s f.
Proof. exact (@lem3618955 A B s f). Qed.
Lemma lem3618957 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term181 A B s f) = (term76 A B f s).
Proof. exact (eq_refl (term181 A B s f)). Qed.
Lemma lem3618958 {A B : Type'} (f : A -> B) (s : A -> Prop) : term76 A B f s.
Proof. exact (EQ_MP (@lem3618957 A B f s) (@lem3618956 A B s f)). Qed.
Lemma lem3618960 {A B : Type'} (f : A -> B) (s : A -> Prop) : term76 A B f s.
Proof. exact (@lem3618297 A B f s (@lem3618958 A B f s)). Qed.
Lemma lem3618961 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term77 A B f s) : False.
Proof. exact (@lem3618960 A B f s (@lem3618281 A B f s h1)). Qed.
Lemma lem3618962 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term77 A B f s) : (term77 A B f s) = False.
Proof. exact (prop_ext (fun h2 : term77 A B f s => @lem3618961 A B f s h1) (fun h2 : False => @lem3618281 A B f s h1)). Qed.
Lemma lem3618963 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term77 A B f s) : False.
Proof. exact (EQ_MP (@lem3618962 A B f s h1) (@lem3618281 A B f s h1)). Qed.
Lemma lem3618964 {A B : Type'} (f : A -> B) (s : A -> Prop) : term76 A B f s.
Proof. exact (fun h0 : term77 A B f s => @lem3618963 A B f s h0). Qed.
Lemma lem3618965 {A B : Type'} (f : A -> B) (s : A -> Prop) : term74 A B f s.
Proof. exact (EQ_MP (@lem3618280 A B f s) (@lem3618964 A B f s)). Qed.
Lemma lem3618966 {A B : Type'} (f : A -> B) (s : A -> Prop) : term38 A B f s.
Proof. exact (EQ_MP (@lem3618276 A B f s) (@lem3618965 A B f s)). Qed.
Lemma lem3618967 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term37 A B f s) = s.
Proof. exact (EQ_MP (@lem3618191 A B f s) (@lem3618966 A B f s)). Qed.
Lemma lem3618968 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term34 A B f s) = (@FINITE A s).
Proof. exact (MK_COMB (@lem3618170 A) (@lem3618967 A B f s)). Qed.
Lemma lem3618969 {A B : Type'} (f : A -> B) (s : A -> Prop) : term182 A B f s.
Proof. exact (@lem3618169 A B f s (@lem3618968 A B f s)). Qed.
Lemma lem3618970 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term32 A B f s) : @FINITE A s.
Proof. exact (@lem3618969 A B f s (@lem3618166 A B f s h1)). Qed.
Lemma lem3618971 {A B : Type'} (f : A -> B) (s : A -> Prop) : term31 A B f s.
Proof. exact (fun h0 : term32 A B f s => @lem3618970 A B f s h0). Qed.
Lemma lem3618972 {A B : Type'} (f : A -> B) (s : A -> Prop) : term30 A B f s.
Proof. exact (EQ_MP (@lem3618160 A B f s) (@lem3618971 A B f s)). Qed.
Lemma lem3618974 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term9 A B s f) : term183 A B f s.
Proof. exact (@lem3618972 A B f s (@lem3617863 A B s f h1)). Qed.
Lemma lem3618975 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term9 A B s f) : term184 A B f s.
Proof. exact (conj (@lem3618974 A B s f h1) (@lem3618134 A B f s)). Qed.
Lemma lem3618976 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term184 A B f s) = ((term14 A B f s) = (@FINITE A s)).
Proof. exact (@lem32 (term14 A B f s) (@FINITE A s)). Qed.
Lemma lem3618977 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term9 A B s f) : (term14 A B f s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3618976 A B f s) (@lem3618975 A B s f h1)). Qed.
Lemma lem3618978 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term9 A B s f) : (term9 A B s f) = ((term14 A B f s) = (@FINITE A s)).
Proof. exact (prop_ext (fun h2 : term9 A B s f => @lem3618977 A B s f h1) (fun h2 : (term14 A B f s) = (@FINITE A s) => @lem3617863 A B s f h1)). Qed.
Lemma lem3618979 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term9 A B s f) : (term14 A B f s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3618978 A B s f h1) (@lem3617863 A B s f h1)). Qed.
Lemma lem3618980 {A B : Type'} (f : A -> B) (s : A -> Prop) : term185 A B f s.
Proof. exact (fun h0 : term9 A B s f => @lem3618979 A B s f h0). Qed.
Lemma lem3618985 {A B : Type'} (f : A -> B) : term186 A B f.
Proof. exact (fun s : A -> Prop => @lem3618980 A B f s). Qed.
Lemma lem3618990 {A B : Type'} : term187 A B.
Proof. exact (fun f : A -> B => @lem3618985 A B f). Qed.
