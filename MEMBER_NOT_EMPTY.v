Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEMBER_NOT_EMPTY_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3215938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3215939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3215938 A s t). Qed.
Lemma lem3215940 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3215939 A s (@EMPTY A)). Qed.
Lemma lem3215949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3215950 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (MK_COMB (@lem3215949) (@lem3215940 A s)). Qed.
Lemma lem3215951 {A : Type'} (s : A -> Prop) : (term4 A s) = (term4 A s).
Proof. exact (eq_refl (term4 A s)). Qed.
Lemma lem3215952 {A : Type'} (s : A -> Prop) : ((term5 A s) = (term2 A s)) = ((term5 A s) = (term3 A s)).
Proof. exact (MK_COMB (@lem3215951 A s) (@lem3215950 A s)). Qed.
Lemma lem3215957 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3215952 A s)). Qed.
Lemma lem3215958 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3215959 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem3215958 A) (@lem3215957 A)). Qed.
Lemma lem3215964 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3215959 A)). Qed.
Lemma lem3215976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3215977 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3215976 A P x). Qed.
Lemma lem3215978 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3215977 A s x). Qed.
Lemma lem3215979 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (fun_ext (fun x : A => @lem3215978 A s x)). Qed.
Lemma lem3215980 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3215981 {A : Type'} (s : A -> Prop) : (term5 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3215980 A) (@lem3215979 A s)). Qed.
Lemma lem3215986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215987 {A : Type'} (s : A -> Prop) : (term4 A s) = (term13 A s).
Proof. exact (MK_COMB (@lem3215986) (@lem3215981 A s)). Qed.
Lemma lem3215995 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3215996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3215995 A P x). Qed.
Lemma lem3215997 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3215996 A s x). Qed.
Lemma lem3215998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3215999 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term15 A s x).
Proof. exact (MK_COMB (@lem3215998) (@lem3215997 A s x)). Qed.
Lemma lem3216001 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3216002 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3216001 A x). Qed.
Lemma lem3216003 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3215999 A s x) (@lem3216002 A x)). Qed.
Lemma lem3216005 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3216006 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term16 A s x).
Proof. exact (@lem3216005 (s x)). Qed.
Lemma lem3216007 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term16 A s x).
Proof. exact (TRANS (@lem3216003 A s x) (@lem3216006 A s x)). Qed.
Lemma lem3216008 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216007 A s x)). Qed.
Lemma lem3216009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216010 {A : Type'} (s : A -> Prop) : (term1 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216009 A) (@lem3216008 A s)). Qed.
Lemma lem3216015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216016 {A : Type'} (s : A -> Prop) : (term3 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem3216015) (@lem3216010 A s)). Qed.
Lemma lem3216017 {A : Type'} (s : A -> Prop) : ((term5 A s) = (term3 A s)) = ((term12 A s) = (term20 A s)).
Proof. exact (MK_COMB (@lem3215987 A s) (@lem3216016 A s)). Qed.
Lemma lem3216020 {A : Type'} : (term7 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3216017 A s)). Qed.
Lemma lem3216021 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216022 {A : Type'} : (term9 A) = (term22 A).
Proof. exact (MK_COMB (@lem3216021 A) (@lem3216020 A)). Qed.
Lemma lem3216027 {A : Type'} : (term22 A) = (term9 A).
Proof. exact (SYM (@lem3216022 A)). Qed.
Lemma lem3216029 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3216030 {A : Type'} : (term22 A) = (term24 A).
Proof. exact (@lem3216029 (term22 A)). Qed.
Lemma lem3216031 {A : Type'} : (term24 A) = (term22 A).
Proof. exact (SYM (@lem3216030 A)). Qed.
Lemma lem3216032 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3216035 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem3216036 {A : Type'} : term26 A.
Proof. exact (fun h0 : term24 A => @lem3216035 A h0). Qed.
Lemma lem3216037 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3216038 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem3216039 {A : Type'} (h1 : term24 A) (h2 : term26 A) : term24 A.
Proof. exact (@lem3216037 A h2 (@lem3216038 A h1)). Qed.
Lemma lem3216040 {A : Type'} (h1 : term24 A) : term27 A.
Proof. exact (fun h0 : term26 A => @lem3216039 A h1 h0). Qed.
Lemma lem3216041 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3216042 {A : Type'} (h1 : term24 A) (h2 : term26 A) : term24 A.
Proof. exact (@lem3216040 A h1 (@lem3216041 A h2)). Qed.
Lemma lem3216043 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (fun h0 : term24 A => @lem3216042 A h0 h1). Qed.
Lemma lem3216044 {A : Type'} : term28 A.
Proof. exact (fun h0 : term26 A => @lem3216043 A h0). Qed.
Lemma lem3216047 {A : Type'} : term26 A.
Proof. exact (@lem3216044 A (@lem3216036 A)). Qed.
Lemma lem3216048 {A : Type'} : term26 A.
Proof. exact (@lem3216047 A). Qed.
Lemma lem3216050 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3216051 {A : Type'} : (term24 A) = (term29 A).
Proof. exact (@lem3216050 (term25 A)). Qed.
Lemma lem3216053 (t : Prop) : (term30 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3216054 {A : Type'} : (term29 A) = (term22 A).
Proof. exact (@lem3216053 (term22 A)). Qed.
Lemma lem3216071 {A : Type'} : (term24 A) = (term22 A).
Proof. exact (TRANS (@lem3216051 A) (@lem3216054 A)). Qed.
Lemma lem3216074 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term16 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3216075 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216074 A s x)). Qed.
Lemma lem3216076 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216077 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216076 A) (@lem3216075 A s)). Qed.
Lemma lem3216078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216079 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem3216078) (@lem3216077 A s)). Qed.
Lemma lem3216080 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3216081 {A : Type'} (s : A -> Prop) : (term11 A s) = (term11 A s).
Proof. exact (fun_ext (fun x : A => @lem3216080 A s x)). Qed.
Lemma lem3216082 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3216083 {A : Type'} (s : A -> Prop) : (term12 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3216082 A) (@lem3216081 A s)). Qed.
Lemma lem3216084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3216085 {A : Type'} (s : A -> Prop) : (term13 A s) = (term13 A s).
Proof. exact (MK_COMB (@lem3216084) (@lem3216083 A s)). Qed.
Lemma lem3216086 {A : Type'} (s : A -> Prop) : ((term12 A s) = (term20 A s)) = ((term12 A s) = (term20 A s)).
Proof. exact (MK_COMB (@lem3216085 A s) (@lem3216079 A s)). Qed.
Lemma lem3216087 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3216086 A s)). Qed.
Lemma lem3216088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3216089 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3216088 A) (@lem3216087 A)). Qed.
Lemma lem3216110 {A : Type'} : (term24 A) = (term22 A).
Proof. exact (TRANS (@lem3216071 A) (@lem3216089 A)). Qed.
Lemma lem3216111 {A : Type'} : (term22 A) = (term24 A).
Proof. exact (SYM (@lem3216110 A)). Qed.
Lemma lem3216113 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3216114 {A : Type'} (s : A -> Prop) : ((term12 A s) = (term20 A s)) = (term31 A s).
Proof. exact (@lem3216113 ((term12 A s) = (term20 A s))). Qed.
Lemma lem3216115 {A : Type'} (s : A -> Prop) : (term31 A s) = ((term12 A s) = (term20 A s)).
Proof. exact (SYM (@lem3216114 A s)). Qed.
Lemma lem3216116 {A : Type'} (s : A -> Prop) (h1 : term32 A s) : term32 A s.
Proof. exact (h1). Qed.
Lemma lem3216118 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3216119 {A : Type'} (P : A -> Prop) : (term33 A P) = (term19 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3216120 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A s).
Proof. exact (@lem3216119 A (term11 A s)). Qed.
Lemma lem3216121 {A : Type'} (s : A -> Prop) (x : A) : (term36 A s x) = (s x).
Proof. exact (eq_refl (term36 A s x)). Qed.
Lemma lem3216122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216124 {A : Type'} (s : A -> Prop) (x : A) : (term37 A s x) = (term16 A s x).
Proof. exact (MK_COMB (@lem3216122) (@lem3216121 A s x)). Qed.
Lemma lem3216125 {A : Type'} (s : A -> Prop) : (term38 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216124 A s x)). Qed.
Lemma lem3216126 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216127 {A : Type'} (s : A -> Prop) : (term35 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216126 A) (@lem3216125 A s)). Qed.
Lemma lem3216128 {A : Type'} (s : A -> Prop) : (term34 A s) = (term19 A s).
Proof. exact (TRANS (@lem3216120 A s) (@lem3216127 A s)). Qed.
Lemma lem3216129 {A : Type'} (s : A -> Prop) : (term11 A s) = (term11 A s).
Proof. exact (fun_ext (fun x : A => @lem3216118 A s x)). Qed.
Lemma lem3216130 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3216131 {A : Type'} (s : A -> Prop) : (term12 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3216130 A) (@lem3216129 A s)). Qed.
Lemma lem3216132 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term16 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3216135 {A : Type'} (s : A -> Prop) (x : A) : (term39 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3216136 {A : Type'} (P : A -> Prop) : (term40 A P) = (term41 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3216137 {A : Type'} (s : A -> Prop) : (term20 A s) = (term42 A s).
Proof. exact (@lem3216136 A (term18 A s)). Qed.
Lemma lem3216138 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term16 A s x).
Proof. exact (eq_refl (term43 A s x)). Qed.
Lemma lem3216139 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216140 {A : Type'} (s : A -> Prop) (x : A) : (term44 A s x) = (term39 A s x).
Proof. exact (MK_COMB (@lem3216139) (@lem3216138 A s x)). Qed.
Lemma lem3216141 {A : Type'} (s : A -> Prop) (x : A) : (term44 A s x) = (s x).
Proof. exact (TRANS (@lem3216140 A s x) (@lem3216135 A s x)). Qed.
Lemma lem3216142 {A : Type'} (s : A -> Prop) : (term45 A s) = (term11 A s).
Proof. exact (fun_ext (fun x : A => @lem3216141 A s x)). Qed.
Lemma lem3216143 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3216144 {A : Type'} (s : A -> Prop) : (term42 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3216143 A) (@lem3216142 A s)). Qed.
Lemma lem3216145 {A : Type'} (s : A -> Prop) : (term20 A s) = (term12 A s).
Proof. exact (TRANS (@lem3216137 A s) (@lem3216144 A s)). Qed.
Lemma lem3216146 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216132 A s x)). Qed.
Lemma lem3216147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216148 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216147 A) (@lem3216146 A s)). Qed.
Lemma lem3216149 {A : Type'} (s : A -> Prop) : (term46 A s) = (term19 A s).
Proof. exact (@lem16933 (term19 A s)). Qed.
Lemma lem3216150 {A : Type'} (s : A -> Prop) : (term46 A s) = (term19 A s).
Proof. exact (TRANS (@lem3216149 A s) (@lem3216148 A s)). Qed.
Lemma lem3216151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216152 {A : Type'} (s : A -> Prop) : (term47 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3216151) (@lem3216128 A s)). Qed.
Lemma lem3216153 {A : Type'} (s : A -> Prop) : (term49 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3216152 A s) (@lem3216145 A s)). Qed.
Lemma lem3216154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216155 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (MK_COMB (@lem3216154) (@lem3216131 A s)). Qed.
Lemma lem3216156 {A : Type'} (s : A -> Prop) : (term52 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem3216155 A s) (@lem3216150 A s)). Qed.
Lemma lem3216157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3216158 {A : Type'} (s : A -> Prop) : (term54 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem3216157) (@lem3216156 A s)). Qed.
Lemma lem3216159 {A : Type'} (s : A -> Prop) : (term56 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem3216158 A s) (@lem3216153 A s)). Qed.
Lemma lem3216160 {A : Type'} (s : A -> Prop) : (term32 A s) = (term56 A s).
Proof. exact (@lem17646 (term12 A s) (term20 A s)). Qed.
Lemma lem3216161 {A : Type'} (s : A -> Prop) : (term32 A s) = (term57 A s).
Proof. exact (TRANS (@lem3216160 A s) (@lem3216159 A s)). Qed.
Lemma lem3216180 {A : Type'} (P : A -> Prop) (Q : Prop) : (term58 A P Q) = (term59 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3216181 {A : Type'} (P : A -> Prop) (Q : Prop) : (term58 A P Q) = (term59 A P Q).
Proof. exact (@lem3216180 A P Q). Qed.
Lemma lem3216182 {A : Type'} (s : A -> Prop) : (term53 A s) = (term60 A s).
Proof. exact (@lem3216181 A s (term19 A s)). Qed.
Lemma lem3216183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3216184 {A : Type'} (s : A -> Prop) : (term55 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3216183) (@lem3216182 A s)). Qed.
Lemma lem3216186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3216187 {A : Type'} (P : Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (@lem3216186 A P Q). Qed.
Lemma lem3216188 {A : Type'} (s : A -> Prop) : (term50 A s) = (term64 A s).
Proof. exact (@lem3216187 A (term19 A s) s). Qed.
Lemma lem3216189 {A : Type'} (s : A -> Prop) : (term57 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem3216184 A s) (@lem3216188 A s)). Qed.
Lemma lem3216191 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3216192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (@lem3216191 A P Q). Qed.
Lemma lem3216193 {A : Type'} (s : A -> Prop) : (term68 A s) = (term69 A s).
Proof. exact (@lem3216192 A (term70 A s) (term71 A s)). Qed.
Lemma lem3216194 {A : Type'} (x : A) (s : A -> Prop) : (term72 A s x) = (term73 A x s).
Proof. exact (eq_refl (term72 A s x)). Qed.
Lemma lem3216195 {A : Type'} (s : A -> Prop) : (term74 A s) = (term70 A s).
Proof. exact (fun_ext (fun x : A => @lem3216194 A x s)). Qed.
Lemma lem3216196 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3216197 {A : Type'} (s : A -> Prop) : (term75 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem3216196 A) (@lem3216195 A s)). Qed.
Lemma lem3216198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3216199 {A : Type'} (s : A -> Prop) : (term76 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3216198) (@lem3216197 A s)). Qed.
Lemma lem3216200 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term78 A s x).
Proof. exact (eq_refl (term77 A s x)). Qed.
Lemma lem3216201 {A : Type'} (s : A -> Prop) : (term79 A s) = (term71 A s).
Proof. exact (fun_ext (fun x : A => @lem3216200 A s x)). Qed.
Lemma lem3216202 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3216203 {A : Type'} (s : A -> Prop) : (term80 A s) = (term64 A s).
Proof. exact (MK_COMB (@lem3216202 A) (@lem3216201 A s)). Qed.
Lemma lem3216204 {A : Type'} (s : A -> Prop) : (term68 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem3216199 A s) (@lem3216203 A s)). Qed.
Lemma lem3216205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3216206 {A : Type'} (s : A -> Prop) : (term81 A s) = (term82 A s).
Proof. exact (MK_COMB (@lem3216205) (@lem3216204 A s)). Qed.
Lemma lem3216207 {A : Type'} (x : A) (s : A -> Prop) : (term72 A s x) = (term73 A x s).
Proof. exact (eq_refl (term72 A s x)). Qed.
Lemma lem3216208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3216209 {A : Type'} (x : A) (s : A -> Prop) : (term83 A s x) = (term84 A x s).
Proof. exact (MK_COMB (@lem3216208) (@lem3216207 A x s)). Qed.
Lemma lem3216210 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term78 A s x).
Proof. exact (eq_refl (term77 A s x)). Qed.
Lemma lem3216211 {A : Type'} (s : A -> Prop) (x : A) : (term85 A s x) = (term86 A s x).
Proof. exact (MK_COMB (@lem3216209 A x s) (@lem3216210 A s x)). Qed.
Lemma lem3216212 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (fun_ext (fun x : A => @lem3216211 A s x)). Qed.
Lemma lem3216213 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3216214 {A : Type'} (s : A -> Prop) : (term69 A s) = (term89 A s).
Proof. exact (MK_COMB (@lem3216213 A) (@lem3216212 A s)). Qed.
Lemma lem3216215 {A : Type'} (s : A -> Prop) : ((term68 A s) = (term69 A s)) = ((term65 A s) = (term89 A s)).
Proof. exact (MK_COMB (@lem3216206 A s) (@lem3216214 A s)). Qed.
Lemma lem3216216 {A : Type'} (s : A -> Prop) : (term65 A s) = (term89 A s).
Proof. exact (EQ_MP (@lem3216215 A s) (@lem3216193 A s)). Qed.
Lemma lem3216218 {A : Type'} (s : A -> Prop) : (term57 A s) = (term89 A s).
Proof. exact (TRANS (@lem3216189 A s) (@lem3216216 A s)). Qed.
Lemma lem3216219 {A : Type'} (s : A -> Prop) : (term32 A s) = (term89 A s).
Proof. exact (TRANS (@lem3216161 A s) (@lem3216218 A s)). Qed.
Lemma lem3216220 {A : Type'} (s : A -> Prop) (h1 : term32 A s) : term89 A s.
Proof. exact (EQ_MP (@lem3216219 A s) (@lem3216116 A s h1)). Qed.
Lemma lem3216221 {A : Type'} (s : A -> Prop) (x : A) (h1 : term86 A s x) : term86 A s x.
Proof. exact (h1). Qed.
Lemma lem3216224 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3216229 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term16 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3216230 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216229 A s x)). Qed.
Lemma lem3216231 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216232 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216231 A) (@lem3216230 A s)). Qed.
Lemma lem3216233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3216234 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3216233) (@lem3216232 A s)). Qed.
Lemma lem3216235 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term78 A s x).
Proof. exact (MK_COMB (@lem3216234 A s) (@lem3216224 A s x)). Qed.
Lemma lem3216240 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term16 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3216241 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216240 A s x)). Qed.
Lemma lem3216242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216243 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216242 A) (@lem3216241 A s)). Qed.
Lemma lem3216248 {A : Type'} (s : A -> Prop) (x : A) : (term90 A s x) = (term90 A s x).
Proof. exact (eq_refl (term90 A s x)). Qed.
Lemma lem3216249 {A : Type'} (x : A) (s : A -> Prop) : (term73 A x s) = (term73 A x s).
Proof. exact (MK_COMB (@lem3216248 A s x) (@lem3216243 A s)). Qed.
Lemma lem3216250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3216251 {A : Type'} (x : A) (s : A -> Prop) : (term84 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem3216250) (@lem3216249 A x s)). Qed.
Lemma lem3216252 {A : Type'} (s : A -> Prop) (x : A) : (term86 A s x) = (term86 A s x).
Proof. exact (MK_COMB (@lem3216251 A x s) (@lem3216235 A s x)). Qed.
Lemma lem3216253 {A : Type'} (s : A -> Prop) (x : A) (h1 : term86 A s x) : term86 A s x.
Proof. exact (EQ_MP (@lem3216252 A s x) (@lem3216221 A s x h1)). Qed.
Lemma lem3216254 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3216255 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem3216256 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term19 A s.
Proof. exact (proj2 (@lem3216254 A x s h1)). Qed.
Lemma lem3216259 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term19 A s.
Proof. exact (proj1 (@lem3216255 A s x h1)). Qed.
Lemma lem3216265 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term16 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3216266 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216265 A s x)). Qed.
Lemma lem3216267 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216269 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216267 A) (@lem3216266 A s)). Qed.
Lemma lem3216270 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term19 A s.
Proof. exact (EQ_MP (@lem3216269 A s) (@lem3216256 A x s h1)). Qed.
Lemma lem3216272 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term16 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3216273 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (fun_ext (fun x : A => @lem3216272 A s x)). Qed.
Lemma lem3216274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216276 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3216274 A) (@lem3216273 A s)). Qed.
Lemma lem3216277 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term19 A s.
Proof. exact (EQ_MP (@lem3216276 A s) (@lem3216259 A s x h1)). Qed.
Lemma lem3216282 {A : Type'} (_33098 : A) (x : A) (s : A -> Prop) (h1 : term73 A x s) : term43 A s _33098.
Proof. exact (@lem3216270 A x s h1 _33098). Qed.
Lemma lem3216283 {A : Type'} (s : A -> Prop) (_33098 : A) : (term43 A s _33098) = (term16 A s _33098).
Proof. exact (eq_refl (term43 A s _33098)). Qed.
Lemma lem3216285 {A : Type'} (_33099 : A) (s : A -> Prop) (x : A) (h1 : term78 A s x) : term43 A s _33099.
Proof. exact (@lem3216277 A s x h1 _33099). Qed.
Lemma lem3216286 {A : Type'} (s : A -> Prop) (_33099 : A) : (term43 A s _33099) = (term16 A s _33099).
Proof. exact (eq_refl (term43 A s _33099)). Qed.
Lemma lem3216291 {A : Type'} (_33098 : A) (x : A) (s : A -> Prop) (h1 : term73 A x s) : term16 A s _33098.
Proof. exact (EQ_MP (@lem3216283 A s _33098) (@lem3216282 A _33098 x s h1)). Qed.
Lemma lem3216293 {A : Type'} (_33099 : A) (s : A -> Prop) (x : A) (h1 : term78 A s x) : term16 A s _33099.
Proof. exact (EQ_MP (@lem3216286 A s _33099) (@lem3216285 A _33099 s x h1)). Qed.
Lemma lem3216297 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : s x.
Proof. exact (proj1 (@lem3216254 A x s h1)). Qed.
Lemma lem3216298 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term91 A s x.
Proof. exact (fun h0 : term16 A s x => @lem3216297 A x s h1). Qed.
Lemma lem3216300 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3216301 {A : Type'} (s : A -> Prop) (x : A) : (term91 A s x) = (s x).
Proof. exact (@lem3216300 (s x)). Qed.
Lemma lem3216302 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : s x.
Proof. exact (EQ_MP (@lem3216301 A s x) (@lem3216298 A x s h1)). Qed.
Lemma lem3216305 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3216307 {A : Type'} (s : A -> Prop) (_33098 : A) : (term16 A s _33098) = (term93 A s _33098).
Proof. exact (@lem3216305 (s _33098)). Qed.
Lemma lem3216310 {A : Type'} (_33098 : A) (x : A) (s : A -> Prop) (h1 : term73 A x s) : term93 A s _33098.
Proof. exact (EQ_MP (@lem3216307 A s _33098) (@lem3216291 A _33098 x s h1)). Qed.
Lemma lem3216311 {A : Type'} (_33098 : A) (x : A) (s : A -> Prop) (h1 : term73 A x s) : term93 A s _33098.
Proof. exact (@lem3216310 A _33098 x s h1). Qed.
Lemma lem3216312 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term93 A s x.
Proof. exact (@lem3216311 A x x s h1). Qed.
Lemma lem3216315 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : False.
Proof. exact (@lem3216312 A x s h1 (@lem3216302 A x s h1)). Qed.
Lemma lem3216316 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term94.
Proof. exact (fun h0 : ~ False => @lem3216315 A x s h1). Qed.
Lemma lem3216318 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3216319 : term94 = False.
Proof. exact (@lem3216318 False). Qed.
Lemma lem3216320 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : False.
Proof. exact (EQ_MP (@lem3216319) (@lem3216316 A x s h1)). Qed.
Lemma lem3216322 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : s x.
Proof. exact (proj2 (@lem3216255 A s x h1)). Qed.
Lemma lem3216323 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term91 A s x.
Proof. exact (fun h0 : term16 A s x => @lem3216322 A s x h1). Qed.
Lemma lem3216325 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3216326 {A : Type'} (s : A -> Prop) (x : A) : (term91 A s x) = (s x).
Proof. exact (@lem3216325 (s x)). Qed.
Lemma lem3216327 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : s x.
Proof. exact (EQ_MP (@lem3216326 A s x) (@lem3216323 A s x h1)). Qed.
Lemma lem3216330 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3216332 {A : Type'} (s : A -> Prop) (_33099 : A) : (term16 A s _33099) = (term93 A s _33099).
Proof. exact (@lem3216330 (s _33099)). Qed.
Lemma lem3216335 {A : Type'} (_33099 : A) (s : A -> Prop) (x : A) (h1 : term78 A s x) : term93 A s _33099.
Proof. exact (EQ_MP (@lem3216332 A s _33099) (@lem3216293 A _33099 s x h1)). Qed.
Lemma lem3216336 {A : Type'} (_33099 : A) (s : A -> Prop) (x : A) (h1 : term78 A s x) : term93 A s _33099.
Proof. exact (@lem3216335 A _33099 s x h1). Qed.
Lemma lem3216337 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term93 A s x.
Proof. exact (@lem3216336 A x s x h1). Qed.
Lemma lem3216340 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : False.
Proof. exact (@lem3216337 A s x h1 (@lem3216327 A s x h1)). Qed.
Lemma lem3216341 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term94.
Proof. exact (fun h0 : ~ False => @lem3216340 A s x h1). Qed.
Lemma lem3216343 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3216344 : term94 = False.
Proof. exact (@lem3216343 False). Qed.
Lemma lem3216345 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : False.
Proof. exact (EQ_MP (@lem3216344) (@lem3216341 A s x h1)). Qed.
Lemma lem3216346 {A : Type'} (s : A -> Prop) (x : A) (h1 : term86 A s x) : False.
Proof. exact (or_elim (@lem3216253 A s x h1) (fun h0 : term73 A x s => @lem3216320 A x s h0) (fun h0 : term78 A s x => @lem3216345 A s x h0)). Qed.
Lemma lem3216347 {A : Type'} (s : A -> Prop) (x : A) (h1 : term86 A s x) : (term86 A s x) = False.
Proof. exact (prop_ext (fun h2 : term86 A s x => @lem3216346 A s x h1) (fun h2 : False => @lem3216253 A s x h1)). Qed.
Lemma lem3216348 {A : Type'} (s : A -> Prop) (x : A) (h1 : term86 A s x) : False.
Proof. exact (EQ_MP (@lem3216347 A s x h1) (@lem3216253 A s x h1)). Qed.
Lemma lem3216349 {A : Type'} (s : A -> Prop) (h1 : term32 A s) : False.
Proof. exact (ex_elim (@lem3216220 A s h1) (fun x : A => fun h0 : term88 A s x => @lem3216348 A s x h0)). Qed.
Lemma lem3216350 {A : Type'} (s : A -> Prop) (h1 : term32 A s) : (term32 A s) = False.
Proof. exact (prop_ext (fun h2 : term32 A s => @lem3216349 A s h1) (fun h2 : False => @lem3216116 A s h1)). Qed.
Lemma lem3216351 {A : Type'} (s : A -> Prop) (h1 : term32 A s) : False.
Proof. exact (EQ_MP (@lem3216350 A s h1) (@lem3216116 A s h1)). Qed.
Lemma lem3216352 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (fun h0 : term32 A s => @lem3216351 A s h0). Qed.
Lemma lem3216353 {A : Type'} (s : A -> Prop) : (term12 A s) = (term20 A s).
Proof. exact (EQ_MP (@lem3216115 A s) (@lem3216352 A s)). Qed.
Lemma lem3216358 {A : Type'} : term22 A.
Proof. exact (fun s : A -> Prop => @lem3216353 A s). Qed.
Lemma lem3216359 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3216111 A) (@lem3216358 A)). Qed.
Lemma lem3216361 {A : Type'} : term24 A.
Proof. exact (@lem3216048 A (@lem3216359 A)). Qed.
Lemma lem3216362 {A : Type'} (h1 : term25 A) : False.
Proof. exact (@lem3216361 A (@lem3216032 A h1)). Qed.
Lemma lem3216363 {A : Type'} (h1 : term25 A) : (term25 A) = False.
Proof. exact (prop_ext (fun h2 : term25 A => @lem3216362 A h1) (fun h2 : False => @lem3216032 A h1)). Qed.
Lemma lem3216364 {A : Type'} (h1 : term25 A) : False.
Proof. exact (EQ_MP (@lem3216363 A h1) (@lem3216032 A h1)). Qed.
Lemma lem3216365 {A : Type'} : term24 A.
Proof. exact (fun h0 : term25 A => @lem3216364 A h0). Qed.
Lemma lem3216366 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3216031 A) (@lem3216365 A)). Qed.
Lemma lem3216367 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3216027 A) (@lem3216366 A)). Qed.
Lemma lem3216368 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3215964 A) (@lem3216367 A)). Qed.
