Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm43208_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Lemma lem42980 (B : Prop) : term0 B.
Proof. exact (@lem9851 B). Qed.
Lemma lem42981 (B : Prop) : (term0 B) = (term1 B).
Proof. exact (eq_refl (term0 B)). Qed.
Lemma lem42982 (B : Prop) : term1 B.
Proof. exact (EQ_MP (@lem42981 B) (@lem42980 B)). Qed.
Lemma lem42983 (B : Prop) (h1 : B = True) : B = True.
Proof. exact (h1). Qed.
Lemma lem42984 (B : Prop) (h1 : B = False) : B = False.
Proof. exact (h1). Qed.
Lemma lem43003 (D : Prop) (A : Prop) (C : Prop) : (term2 D A C) = (term2 D A C).
Proof. exact (eq_refl (term2 D A C)). Qed.
Lemma lem43004 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = True) : (term3 D A C B) = (term4 D A C).
Proof. exact (MK_COMB (@lem43003 D A C) (@lem42983 B h1)). Qed.
Lemma lem43005 (D : Prop) (A : Prop) (C : Prop) : (term4 D A C) = (term5 D A C).
Proof. exact (eq_refl (term4 D A C)). Qed.
Lemma lem43006 (D : Prop) (A : Prop) (C : Prop) (B : Prop) : (term6 D A C B) = (term6 D A C B).
Proof. exact (eq_refl (term6 D A C B)). Qed.
Lemma lem43007 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : ((term3 D A C B) = (term4 D A C)) = ((term3 D A C B) = (term5 D A C)).
Proof. exact (MK_COMB (@lem43006 D A C B) (@lem43005 D A C)). Qed.
Lemma lem43008 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : (term3 D A C B) = (term7 B D A C).
Proof. exact (eq_refl (term3 D A C B)). Qed.
Lemma lem43009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem43010 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : (term6 D A C B) = (term8 B D A C).
Proof. exact (MK_COMB (@lem43009) (@lem43008 B D A C)). Qed.
Lemma lem43011 (D : Prop) (A : Prop) (C : Prop) : (term5 D A C) = (term5 D A C).
Proof. exact (eq_refl (term5 D A C)). Qed.
Lemma lem43012 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : ((term3 D A C B) = (term5 D A C)) = ((term7 B D A C) = (term5 D A C)).
Proof. exact (MK_COMB (@lem43010 B D A C) (@lem43011 D A C)). Qed.
Lemma lem43013 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : ((term3 D A C B) = (term4 D A C)) = ((term7 B D A C) = (term5 D A C)).
Proof. exact (TRANS (@lem43007 B D A C) (@lem43012 B D A C)). Qed.
Lemma lem43014 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = True) : (term7 B D A C) = (term5 D A C).
Proof. exact (EQ_MP (@lem43013 B D A C) (@lem43004 D A C B h1)). Qed.
Lemma lem43015 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = True) : (term5 D A C) = (term7 B D A C).
Proof. exact (SYM (@lem43014 D A C B h1)). Qed.
Lemma lem43016 (D : Prop) (A : Prop) (C : Prop) : (term2 D A C) = (term2 D A C).
Proof. exact (eq_refl (term2 D A C)). Qed.
Lemma lem43017 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = False) : (term3 D A C B) = (term9 D A C).
Proof. exact (MK_COMB (@lem43016 D A C) (@lem42984 B h1)). Qed.
Lemma lem43018 (D : Prop) (A : Prop) (C : Prop) : (term9 D A C) = (term10 D A C).
Proof. exact (eq_refl (term9 D A C)). Qed.
Lemma lem43019 (D : Prop) (A : Prop) (C : Prop) (B : Prop) : (term6 D A C B) = (term6 D A C B).
Proof. exact (eq_refl (term6 D A C B)). Qed.
Lemma lem43020 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : ((term3 D A C B) = (term9 D A C)) = ((term3 D A C B) = (term10 D A C)).
Proof. exact (MK_COMB (@lem43019 D A C B) (@lem43018 D A C)). Qed.
Lemma lem43021 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : (term3 D A C B) = (term7 B D A C).
Proof. exact (eq_refl (term3 D A C B)). Qed.
Lemma lem43022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem43023 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : (term6 D A C B) = (term8 B D A C).
Proof. exact (MK_COMB (@lem43022) (@lem43021 B D A C)). Qed.
Lemma lem43024 (D : Prop) (A : Prop) (C : Prop) : (term10 D A C) = (term10 D A C).
Proof. exact (eq_refl (term10 D A C)). Qed.
Lemma lem43025 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : ((term3 D A C B) = (term10 D A C)) = ((term7 B D A C) = (term10 D A C)).
Proof. exact (MK_COMB (@lem43023 B D A C) (@lem43024 D A C)). Qed.
Lemma lem43026 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : ((term3 D A C B) = (term9 D A C)) = ((term7 B D A C) = (term10 D A C)).
Proof. exact (TRANS (@lem43020 B D A C) (@lem43025 B D A C)). Qed.
Lemma lem43027 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = False) : (term7 B D A C) = (term10 D A C).
Proof. exact (EQ_MP (@lem43026 B D A C) (@lem43017 D A C B h1)). Qed.
Lemma lem43028 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = False) : (term10 D A C) = (term7 B D A C).
Proof. exact (SYM (@lem43027 D A C B h1)). Qed.
Lemma lem43034 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem43035 (A : Prop) : (True -> A) = A.
Proof. exact (@lem43034 A). Qed.
Lemma lem43036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem43037 (A : Prop) : (term11 A) = (and A).
Proof. exact (MK_COMB (@lem43036) (@lem43035 A)). Qed.
Lemma lem43039 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem43040 (D : Prop) (C : Prop) : (term12 D C) = (D -> C).
Proof. exact (@lem43039 (D -> C)). Qed.
Lemma lem43043 (A : Prop) (D : Prop) (C : Prop) : (term13 A D C) = (term14 A D C).
Proof. exact (MK_COMB (@lem43037 A) (@lem43040 D C)). Qed.
Lemma lem43046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem43047 (A : Prop) (D : Prop) (C : Prop) : (term15 A D C) = (term16 A D C).
Proof. exact (MK_COMB (@lem43046) (@lem43043 A D C)). Qed.
Lemma lem43051 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem43052 (D : Prop) : (True /\ D) = D.
Proof. exact (@lem43051 D). Qed.
Lemma lem43053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem43054 (D : Prop) : (term17 D) = (imp D).
Proof. exact (MK_COMB (@lem43053) (@lem43052 D)). Qed.
Lemma lem43057 (A : Prop) (C : Prop) : (A /\ C) = (A /\ C).
Proof. exact (eq_refl (A /\ C)). Qed.
Lemma lem43058 (D : Prop) (A : Prop) (C : Prop) : (term18 D A C) = (term19 D A C).
Proof. exact (MK_COMB (@lem43054 D) (@lem43057 A C)). Qed.
Lemma lem43061 (D : Prop) (A : Prop) (C : Prop) : (term5 D A C) = (term20 D A C).
Proof. exact (MK_COMB (@lem43047 A D C) (@lem43058 D A C)). Qed.
Lemma lem43064 (D : Prop) (A : Prop) (C : Prop) : (term20 D A C) = (term5 D A C).
Proof. exact (SYM (@lem43061 D A C)). Qed.
Lemma lem43065 (A : Prop) : term0 A.
Proof. exact (@lem9851 A). Qed.
Lemma lem43066 (A : Prop) : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem43067 (A : Prop) : term1 A.
Proof. exact (EQ_MP (@lem43066 A) (@lem43065 A)). Qed.
Lemma lem43068 (A : Prop) (h1 : A = True) : A = True.
Proof. exact (h1). Qed.
Lemma lem43069 (A : Prop) (h1 : A = False) : A = False.
Proof. exact (h1). Qed.
Lemma lem43082 (D : Prop) (C : Prop) : (term21 D C) = (term21 D C).
Proof. exact (eq_refl (term21 D C)). Qed.
Lemma lem43083 (D : Prop) (C : Prop) (A : Prop) (h1 : A = True) : (term22 D C A) = (term23 D C).
Proof. exact (MK_COMB (@lem43082 D C) (@lem43068 A h1)). Qed.
Lemma lem43084 (D : Prop) (C : Prop) : (term23 D C) = (term24 D C).
Proof. exact (eq_refl (term23 D C)). Qed.
Lemma lem43085 (D : Prop) (C : Prop) (A : Prop) : (term25 D C A) = (term25 D C A).
Proof. exact (eq_refl (term25 D C A)). Qed.
Lemma lem43086 (A : Prop) (D : Prop) (C : Prop) : ((term22 D C A) = (term23 D C)) = ((term22 D C A) = (term24 D C)).
Proof. exact (MK_COMB (@lem43085 D C A) (@lem43084 D C)). Qed.
Lemma lem43087 (D : Prop) (A : Prop) (C : Prop) : (term22 D C A) = (term20 D A C).
Proof. exact (eq_refl (term22 D C A)). Qed.
Lemma lem43088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem43089 (D : Prop) (A : Prop) (C : Prop) : (term25 D C A) = (term26 D A C).
Proof. exact (MK_COMB (@lem43088) (@lem43087 D A C)). Qed.
Lemma lem43090 (D : Prop) (C : Prop) : (term24 D C) = (term24 D C).
Proof. exact (eq_refl (term24 D C)). Qed.
Lemma lem43091 (A : Prop) (D : Prop) (C : Prop) : ((term22 D C A) = (term24 D C)) = ((term20 D A C) = (term24 D C)).
Proof. exact (MK_COMB (@lem43089 D A C) (@lem43090 D C)). Qed.
Lemma lem43092 (A : Prop) (D : Prop) (C : Prop) : ((term22 D C A) = (term23 D C)) = ((term20 D A C) = (term24 D C)).
Proof. exact (TRANS (@lem43086 A D C) (@lem43091 A D C)). Qed.
Lemma lem43093 (D : Prop) (C : Prop) (A : Prop) (h1 : A = True) : (term20 D A C) = (term24 D C).
Proof. exact (EQ_MP (@lem43092 A D C) (@lem43083 D C A h1)). Qed.
Lemma lem43094 (D : Prop) (C : Prop) (A : Prop) (h1 : A = True) : (term24 D C) = (term20 D A C).
Proof. exact (SYM (@lem43093 D C A h1)). Qed.
Lemma lem43095 (D : Prop) (C : Prop) : (term21 D C) = (term21 D C).
Proof. exact (eq_refl (term21 D C)). Qed.
Lemma lem43096 (D : Prop) (C : Prop) (A : Prop) (h1 : A = False) : (term22 D C A) = (term27 D C).
Proof. exact (MK_COMB (@lem43095 D C) (@lem43069 A h1)). Qed.
Lemma lem43097 (D : Prop) (C : Prop) : (term27 D C) = (term28 D C).
Proof. exact (eq_refl (term27 D C)). Qed.
Lemma lem43098 (D : Prop) (C : Prop) (A : Prop) : (term25 D C A) = (term25 D C A).
Proof. exact (eq_refl (term25 D C A)). Qed.
Lemma lem43099 (A : Prop) (D : Prop) (C : Prop) : ((term22 D C A) = (term27 D C)) = ((term22 D C A) = (term28 D C)).
Proof. exact (MK_COMB (@lem43098 D C A) (@lem43097 D C)). Qed.
Lemma lem43100 (D : Prop) (A : Prop) (C : Prop) : (term22 D C A) = (term20 D A C).
Proof. exact (eq_refl (term22 D C A)). Qed.
Lemma lem43101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem43102 (D : Prop) (A : Prop) (C : Prop) : (term25 D C A) = (term26 D A C).
Proof. exact (MK_COMB (@lem43101) (@lem43100 D A C)). Qed.
Lemma lem43103 (D : Prop) (C : Prop) : (term28 D C) = (term28 D C).
Proof. exact (eq_refl (term28 D C)). Qed.
Lemma lem43104 (A : Prop) (D : Prop) (C : Prop) : ((term22 D C A) = (term28 D C)) = ((term20 D A C) = (term28 D C)).
Proof. exact (MK_COMB (@lem43102 D A C) (@lem43103 D C)). Qed.
Lemma lem43105 (A : Prop) (D : Prop) (C : Prop) : ((term22 D C A) = (term27 D C)) = ((term20 D A C) = (term28 D C)).
Proof. exact (TRANS (@lem43099 A D C) (@lem43104 A D C)). Qed.
Lemma lem43106 (D : Prop) (C : Prop) (A : Prop) (h1 : A = False) : (term20 D A C) = (term28 D C).
Proof. exact (EQ_MP (@lem43105 A D C) (@lem43096 D C A h1)). Qed.
Lemma lem43107 (D : Prop) (C : Prop) (A : Prop) (h1 : A = False) : (term28 D C) = (term20 D A C).
Proof. exact (SYM (@lem43106 D C A h1)). Qed.
Lemma lem43111 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem43112 (D : Prop) (C : Prop) : (term29 D C) = (D -> C).
Proof. exact (@lem43111 (D -> C)). Qed.
Lemma lem43115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem43116 (D : Prop) (C : Prop) : (term30 D C) = (term31 D C).
Proof. exact (MK_COMB (@lem43115) (@lem43112 D C)). Qed.
Lemma lem43120 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem43121 (C : Prop) : (True /\ C) = C.
Proof. exact (@lem43120 C). Qed.
Lemma lem43122 (D : Prop) : (imp D) = (imp D).
Proof. exact (eq_refl (imp D)). Qed.
Lemma lem43123 (D : Prop) (C : Prop) : (term32 D C) = (D -> C).
Proof. exact (MK_COMB (@lem43122 D) (@lem43121 C)). Qed.
Lemma lem43126 (D : Prop) (C : Prop) : (term24 D C) = (term33 D C).
Proof. exact (MK_COMB (@lem43116 D C) (@lem43123 D C)). Qed.
Lemma lem43128 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem43129 (D : Prop) (C : Prop) : (term33 D C) = True.
Proof. exact (@lem43128 (D -> C)). Qed.
Lemma lem43130 (D : Prop) (C : Prop) : (term24 D C) = True.
Proof. exact (TRANS (@lem43126 D C) (@lem43129 D C)). Qed.
Lemma lem43131 (D : Prop) (C : Prop) : True = (term24 D C).
Proof. exact (SYM (@lem43130 D C)). Qed.
Lemma lem43132 (D : Prop) (C : Prop) : term24 D C.
Proof. exact (EQ_MP (@lem43131 D C) (@lem0)). Qed.
Lemma lem43136 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem43137 (D : Prop) (C : Prop) : (term34 D C) = False.
Proof. exact (@lem43136 (D -> C)). Qed.
Lemma lem43138 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem43139 (D : Prop) (C : Prop) : (term35 D C) = (imp False).
Proof. exact (MK_COMB (@lem43138) (@lem43137 D C)). Qed.
Lemma lem43143 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem43144 (C : Prop) : (False /\ C) = False.
Proof. exact (@lem43143 C). Qed.
Lemma lem43145 (D : Prop) : (imp D) = (imp D).
Proof. exact (eq_refl (imp D)). Qed.
Lemma lem43146 (C : Prop) (D : Prop) : (term36 D C) = (D -> False).
Proof. exact (MK_COMB (@lem43145 D) (@lem43144 C)). Qed.
Lemma lem43148 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem43149 (D : Prop) : (D -> False) = (~ D).
Proof. exact (@lem43148 D). Qed.
Lemma lem43150 (C : Prop) (D : Prop) : (term36 D C) = (~ D).
Proof. exact (TRANS (@lem43146 C D) (@lem43149 D)). Qed.
Lemma lem43151 (C : Prop) (D : Prop) : (term28 D C) = (term37 D).
Proof. exact (MK_COMB (@lem43139 D C) (@lem43150 C D)). Qed.
Lemma lem43153 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem43154 (D : Prop) : (term37 D) = True.
Proof. exact (@lem43153 (~ D)). Qed.
Lemma lem43155 (D : Prop) (C : Prop) : (term28 D C) = True.
Proof. exact (TRANS (@lem43151 C D) (@lem43154 D)). Qed.
Lemma lem43156 (D : Prop) (C : Prop) : True = (term28 D C).
Proof. exact (SYM (@lem43155 D C)). Qed.
Lemma lem43157 (D : Prop) (C : Prop) : term28 D C.
Proof. exact (EQ_MP (@lem43156 D C) (@lem0)). Qed.
Lemma lem43158 (D : Prop) (C : Prop) (A : Prop) (h1 : A = False) : term20 D A C.
Proof. exact (EQ_MP (@lem43107 D C A h1) (@lem43157 D C)). Qed.
Lemma lem43159 (D : Prop) (C : Prop) (A : Prop) (h1 : A = True) : term20 D A C.
Proof. exact (EQ_MP (@lem43094 D C A h1) (@lem43132 D C)). Qed.
Lemma lem43161 (D : Prop) (A : Prop) (C : Prop) : term20 D A C.
Proof. exact (or_elim (@lem43067 A) (fun h0 : A = True => @lem43159 D C A h0) (fun h0 : A = False => @lem43158 D C A h0)). Qed.
Lemma lem43162 (D : Prop) (A : Prop) (C : Prop) : term5 D A C.
Proof. exact (EQ_MP (@lem43064 D A C) (@lem43161 D A C)). Qed.
Lemma lem43168 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem43169 (A : Prop) : (False -> A) = True.
Proof. exact (@lem43168 A). Qed.
Lemma lem43170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem43171 (A : Prop) : (term38 A) = (and True).
Proof. exact (MK_COMB (@lem43170) (@lem43169 A)). Qed.
Lemma lem43173 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem43174 (D : Prop) (C : Prop) : (term39 D C) = True.
Proof. exact (@lem43173 (D -> C)). Qed.
Lemma lem43175 (A : Prop) (D : Prop) (C : Prop) : (term40 A D C) = (True /\ True).
Proof. exact (MK_COMB (@lem43171 A) (@lem43174 D C)). Qed.
Lemma lem43177 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem43178 : (True /\ True) = True.
Proof. exact (@lem43177 True). Qed.
Lemma lem43179 (A : Prop) (D : Prop) (C : Prop) : (term40 A D C) = True.
Proof. exact (TRANS (@lem43175 A D C) (@lem43178)). Qed.
Lemma lem43180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem43181 (A : Prop) (D : Prop) (C : Prop) : (term41 A D C) = (imp True).
Proof. exact (MK_COMB (@lem43180) (@lem43179 A D C)). Qed.
Lemma lem43185 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem43186 (D : Prop) : (False /\ D) = False.
Proof. exact (@lem43185 D). Qed.
Lemma lem43187 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem43188 (D : Prop) : (term42 D) = (imp False).
Proof. exact (MK_COMB (@lem43187) (@lem43186 D)). Qed.
Lemma lem43191 (A : Prop) (C : Prop) : (A /\ C) = (A /\ C).
Proof. exact (eq_refl (A /\ C)). Qed.
Lemma lem43192 (D : Prop) (A : Prop) (C : Prop) : (term43 D A C) = (term44 A C).
Proof. exact (MK_COMB (@lem43188 D) (@lem43191 A C)). Qed.
Lemma lem43194 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem43195 (A : Prop) (C : Prop) : (term44 A C) = True.
Proof. exact (@lem43194 (A /\ C)). Qed.
Lemma lem43196 (D : Prop) (A : Prop) (C : Prop) : (term43 D A C) = True.
Proof. exact (TRANS (@lem43192 D A C) (@lem43195 A C)). Qed.
Lemma lem43197 (D : Prop) (A : Prop) (C : Prop) : (term10 D A C) = (True -> True).
Proof. exact (MK_COMB (@lem43181 A D C) (@lem43196 D A C)). Qed.
Lemma lem43199 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem43200 : (True -> True) = True.
Proof. exact (@lem43199 True). Qed.
Lemma lem43201 (D : Prop) (A : Prop) (C : Prop) : (term10 D A C) = True.
Proof. exact (TRANS (@lem43197 D A C) (@lem43200)). Qed.
Lemma lem43202 (D : Prop) (A : Prop) (C : Prop) : True = (term10 D A C).
Proof. exact (SYM (@lem43201 D A C)). Qed.
Lemma lem43203 (D : Prop) (A : Prop) (C : Prop) : term10 D A C.
Proof. exact (EQ_MP (@lem43202 D A C) (@lem0)). Qed.
Lemma lem43204 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = False) : term7 B D A C.
Proof. exact (EQ_MP (@lem43028 D A C B h1) (@lem43203 D A C)). Qed.
Lemma lem43205 (D : Prop) (A : Prop) (C : Prop) (B : Prop) (h1 : B = True) : term7 B D A C.
Proof. exact (EQ_MP (@lem43015 D A C B h1) (@lem43162 D A C)). Qed.
Lemma lem43208 (B : Prop) (D : Prop) (A : Prop) (C : Prop) : term7 B D A C.
Proof. exact (or_elim (@lem42982 B) (fun h0 : B = True => @lem43205 D A C B h0) (fun h0 : B = False => @lem43204 D A C B h0)). Qed.
