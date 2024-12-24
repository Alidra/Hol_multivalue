Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_SUPERSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import INFINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm69_spec.
Lemma lem3734934 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3734935 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3734936 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3734935 t1) (@lem3734934 t1)). Qed.
Lemma lem3734937 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3734936 t1 t2). Qed.
Lemma lem3734938 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3734939 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3734938 t1 t2) (@lem3734937 t1 t2)). Qed.
Lemma lem3734940 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3734939 t1 t2 t3). Qed.
Lemma lem3734941 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3734942 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3734941 t1 t2 t3) (@lem3734940 t1 t2 t3)). Qed.
Lemma lem3734943 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3734942 t1 t2 t3)). Qed.
Lemma lem3734944 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem3734945 {A : Type'} (s : A -> Prop) : (term7 A s) = ((@INFINITE A s) = (term8 A s)).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3734960 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term8 A s).
Proof. exact (EQ_MP (@lem3734945 A s) (@lem3734944 A s)). Qed.
Lemma lem3734961 {_97990 : Type'} (s : _97990 -> Prop) : (@INFINITE _97990 s) = (term8 _97990 s).
Proof. exact (@lem3734960 _97990 s). Qed.
Lemma lem3734962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3734963 {_97990 : Type'} (s : _97990 -> Prop) : (term9 _97990 s) = (term10 _97990 s).
Proof. exact (MK_COMB (@lem3734962) (@lem3734961 _97990 s)). Qed.
Lemma lem3734964 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (@SUBSET _97990 s t) = (@SUBSET _97990 s t).
Proof. exact (eq_refl (@SUBSET _97990 s t)). Qed.
Lemma lem3734965 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term11 _97990 s t) = (term12 _97990 s t).
Proof. exact (MK_COMB (@lem3734963 _97990 s) (@lem3734964 _97990 s t)). Qed.
Lemma lem3734968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3734969 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term13 _97990 s t) = (term14 _97990 s t).
Proof. exact (MK_COMB (@lem3734968) (@lem3734965 _97990 s t)). Qed.
Lemma lem3734971 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term8 A s).
Proof. exact (EQ_MP (@lem3734945 A s) (@lem3734944 A s)). Qed.
Lemma lem3734972 {_97990 : Type'} (s : _97990 -> Prop) : (@INFINITE _97990 s) = (term8 _97990 s).
Proof. exact (@lem3734971 _97990 s). Qed.
Lemma lem3734973 {_97990 : Type'} (t : _97990 -> Prop) : (@INFINITE _97990 t) = (term8 _97990 t).
Proof. exact (@lem3734972 _97990 t). Qed.
Lemma lem3734974 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term15 _97990 s t) = (term16 _97990 s t).
Proof. exact (MK_COMB (@lem3734969 _97990 s t) (@lem3734973 _97990 t)). Qed.
Lemma lem3734977 {_97990 : Type'} (s : _97990 -> Prop) : (term17 _97990 s) = (term18 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3734974 _97990 s t)). Qed.
Lemma lem3734978 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3734979 {_97990 : Type'} (s : _97990 -> Prop) : (term19 _97990 s) = (term20 _97990 s).
Proof. exact (MK_COMB (@lem3734978 _97990) (@lem3734977 _97990 s)). Qed.
Lemma lem3734984 {_97990 : Type'} : (term21 _97990) = (term22 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3734979 _97990 s)). Qed.
Lemma lem3734985 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3734986 {_97990 : Type'} : (term23 _97990) = (term24 _97990).
Proof. exact (MK_COMB (@lem3734985 _97990) (@lem3734984 _97990)). Qed.
Lemma lem3734991 {_97990 : Type'} : (term24 _97990) = (term23 _97990).
Proof. exact (SYM (@lem3734986 _97990)). Qed.
Lemma lem3734993 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3734994 {_97990 : Type'} : (term24 _97990) = (term26 _97990).
Proof. exact (@lem3734993 (term24 _97990)). Qed.
Lemma lem3734995 {_97990 : Type'} : (term26 _97990) = (term24 _97990).
Proof. exact (SYM (@lem3734994 _97990)). Qed.
Lemma lem3734996 {_97990 : Type'} (h1 : term27 _97990) : term27 _97990.
Proof. exact (h1). Qed.
Lemma lem3734997 {_97990 : Type'} : term28 _97990.
Proof. exact (@lem3599924 _97990). Qed.
Lemma lem3735001 {_97990 : Type'} (h1 : term29 _97990) : term29 _97990.
Proof. exact (h1). Qed.
Lemma lem3735002 {_97990 : Type'} : term30 _97990.
Proof. exact (fun h0 : term29 _97990 => @lem3735001 _97990 h0). Qed.
Lemma lem3735003 {_97990 : Type'} (h1 : term30 _97990) : term30 _97990.
Proof. exact (h1). Qed.
Lemma lem3735004 {_97990 : Type'} (h1 : term29 _97990) : term29 _97990.
Proof. exact (h1). Qed.
Lemma lem3735005 {_97990 : Type'} (h1 : term29 _97990) (h2 : term30 _97990) : term29 _97990.
Proof. exact (@lem3735003 _97990 h2 (@lem3735004 _97990 h1)). Qed.
Lemma lem3735006 {_97990 : Type'} (h1 : term29 _97990) : term31 _97990.
Proof. exact (fun h0 : term30 _97990 => @lem3735005 _97990 h1 h0). Qed.
Lemma lem3735007 {_97990 : Type'} (h1 : term30 _97990) : term30 _97990.
Proof. exact (h1). Qed.
Lemma lem3735008 {_97990 : Type'} (h1 : term29 _97990) (h2 : term30 _97990) : term29 _97990.
Proof. exact (@lem3735006 _97990 h1 (@lem3735007 _97990 h2)). Qed.
Lemma lem3735009 {_97990 : Type'} (h1 : term30 _97990) : term30 _97990.
Proof. exact (fun h0 : term29 _97990 => @lem3735008 _97990 h0 h1). Qed.
Lemma lem3735010 {_97990 : Type'} : term32 _97990.
Proof. exact (fun h0 : term30 _97990 => @lem3735009 _97990 h0). Qed.
Lemma lem3735013 {_97990 : Type'} : term30 _97990.
Proof. exact (@lem3735010 _97990 (@lem3735002 _97990)). Qed.
Lemma lem3735014 {_97990 : Type'} : term30 _97990.
Proof. exact (@lem3735013 _97990). Qed.
Lemma lem3735030 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3735031 {_97990 : Type'} : (term33 _97990) = (term34 _97990).
Proof. exact (@lem3735030 (term28 _97990)). Qed.
Lemma lem3735044 {_97990 : Type'} : (term35 _97990) = (term35 _97990).
Proof. exact (eq_refl (term35 _97990)). Qed.
Lemma lem3735051 {_97990 : Type'} : (term29 _97990) = (term36 _97990).
Proof. exact (MK_COMB (@lem3735044 _97990) (@lem3735031 _97990)). Qed.
Lemma lem3735060 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term37 _97990 t s) = (term37 _97990 t s).
Proof. exact (eq_refl (term37 _97990 t s)). Qed.
Lemma lem3735061 {_97990 : Type'} (s : _97990 -> Prop) : (term38 _97990 s) = (term38 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735060 _97990 t s)). Qed.
Lemma lem3735062 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735063 {_97990 : Type'} (s : _97990 -> Prop) : (term39 _97990 s) = (term39 _97990 s).
Proof. exact (MK_COMB (@lem3735062 _97990) (@lem3735061 _97990 s)). Qed.
Lemma lem3735064 {_97990 : Type'} : (term40 _97990) = (term40 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735063 _97990 s)). Qed.
Lemma lem3735065 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735066 {_97990 : Type'} : (term28 _97990) = (term28 _97990).
Proof. exact (MK_COMB (@lem3735065 _97990) (@lem3735064 _97990)). Qed.
Lemma lem3735067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3735068 {_97990 : Type'} : (term34 _97990) = (term34 _97990).
Proof. exact (MK_COMB (@lem3735067) (@lem3735066 _97990)). Qed.
Lemma lem3735081 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term16 _97990 s t) = (term16 _97990 s t).
Proof. exact (eq_refl (term16 _97990 s t)). Qed.
Lemma lem3735082 {_97990 : Type'} (s : _97990 -> Prop) : (term18 _97990 s) = (term18 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735081 _97990 s t)). Qed.
Lemma lem3735083 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735084 {_97990 : Type'} (s : _97990 -> Prop) : (term20 _97990 s) = (term20 _97990 s).
Proof. exact (MK_COMB (@lem3735083 _97990) (@lem3735082 _97990 s)). Qed.
Lemma lem3735085 {_97990 : Type'} : (term22 _97990) = (term22 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735084 _97990 s)). Qed.
Lemma lem3735086 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735087 {_97990 : Type'} : (term24 _97990) = (term24 _97990).
Proof. exact (MK_COMB (@lem3735086 _97990) (@lem3735085 _97990)). Qed.
Lemma lem3735088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3735089 {_97990 : Type'} : (term27 _97990) = (term27 _97990).
Proof. exact (MK_COMB (@lem3735088) (@lem3735087 _97990)). Qed.
Lemma lem3735090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3735091 {_97990 : Type'} : (term35 _97990) = (term35 _97990).
Proof. exact (MK_COMB (@lem3735090) (@lem3735089 _97990)). Qed.
Lemma lem3735092 {_97990 : Type'} : (term36 _97990) = (term36 _97990).
Proof. exact (MK_COMB (@lem3735091 _97990) (@lem3735068 _97990)). Qed.
Lemma lem3735129 {_97990 : Type'} : (term29 _97990) = (term36 _97990).
Proof. exact (TRANS (@lem3735051 _97990) (@lem3735092 _97990)). Qed.
Lemma lem3735130 {_97990 : Type'} : (term36 _97990) = (term29 _97990).
Proof. exact (SYM (@lem3735129 _97990)). Qed.
Lemma lem3735131 {_97990 : Type'} (h1 : term27 _97990) : term27 _97990.
Proof. exact (h1). Qed.
Lemma lem3735132 {_97990 : Type'} (h1 : term28 _97990) : term28 _97990.
Proof. exact (h1). Qed.
Lemma lem3735140 {_97990 : Type'} (t : _97990 -> Prop) : (term41 _97990 t) = (@FINITE _97990 t).
Proof. exact (@lem16933 (@FINITE _97990 t)). Qed.
Lemma lem3735142 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term42 _97990 s t) = (term42 _97990 s t).
Proof. exact (eq_refl (term42 _97990 s t)). Qed.
Lemma lem3735143 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term43 _97990 s t) = (term44 _97990 s t).
Proof. exact (MK_COMB (@lem3735142 _97990 s t) (@lem3735140 _97990 t)). Qed.
Lemma lem3735144 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term45 _97990 s t) = (term43 _97990 s t).
Proof. exact (@lem17362 (term12 _97990 s t) (term8 _97990 t)). Qed.
Lemma lem3735145 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term45 _97990 s t) = (term44 _97990 s t).
Proof. exact (TRANS (@lem3735144 _97990 s t) (@lem3735143 _97990 s t)). Qed.
Lemma lem3735146 {_97990 : Type'} (P : type686 _97990) : (term46 _97990 P) = (term47 _97990 P).
Proof. exact (@lem18392 (_97990 -> Prop) P). Qed.
Lemma lem3735147 {_97990 : Type'} (s : _97990 -> Prop) : (term48 _97990 s) = (term49 _97990 s).
Proof. exact (@lem3735146 _97990 (term18 _97990 s)). Qed.
Lemma lem3735148 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term50 _97990 s t) = (term16 _97990 s t).
Proof. exact (eq_refl (term50 _97990 s t)). Qed.
Lemma lem3735149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3735150 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term51 _97990 s t) = (term45 _97990 s t).
Proof. exact (MK_COMB (@lem3735149) (@lem3735148 _97990 s t)). Qed.
Lemma lem3735151 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term51 _97990 s t) = (term44 _97990 s t).
Proof. exact (TRANS (@lem3735150 _97990 s t) (@lem3735145 _97990 s t)). Qed.
Lemma lem3735152 {_97990 : Type'} (s : _97990 -> Prop) : (term52 _97990 s) = (term53 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735151 _97990 s t)). Qed.
Lemma lem3735153 {_97990 : Type'} : (@ex (_97990 -> Prop)) = (@ex (_97990 -> Prop)).
Proof. exact (eq_refl (@ex (_97990 -> Prop))). Qed.
Lemma lem3735154 {_97990 : Type'} (s : _97990 -> Prop) : (term49 _97990 s) = (term54 _97990 s).
Proof. exact (MK_COMB (@lem3735153 _97990) (@lem3735152 _97990 s)). Qed.
Lemma lem3735155 {_97990 : Type'} (s : _97990 -> Prop) : (term48 _97990 s) = (term54 _97990 s).
Proof. exact (TRANS (@lem3735147 _97990 s) (@lem3735154 _97990 s)). Qed.
Lemma lem3735156 {_97990 : Type'} (P : type686 _97990) : (term46 _97990 P) = (term47 _97990 P).
Proof. exact (@lem18392 (_97990 -> Prop) P). Qed.
Lemma lem3735157 {_97990 : Type'} : (term27 _97990) = (term55 _97990).
Proof. exact (@lem3735156 _97990 (term22 _97990)). Qed.
Lemma lem3735158 {_97990 : Type'} (s : _97990 -> Prop) : (term56 _97990 s) = (term20 _97990 s).
Proof. exact (eq_refl (term56 _97990 s)). Qed.
Lemma lem3735159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3735160 {_97990 : Type'} (s : _97990 -> Prop) : (term57 _97990 s) = (term48 _97990 s).
Proof. exact (MK_COMB (@lem3735159) (@lem3735158 _97990 s)). Qed.
Lemma lem3735161 {_97990 : Type'} (s : _97990 -> Prop) : (term57 _97990 s) = (term54 _97990 s).
Proof. exact (TRANS (@lem3735160 _97990 s) (@lem3735155 _97990 s)). Qed.
Lemma lem3735162 {_97990 : Type'} : (term58 _97990) = (term59 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735161 _97990 s)). Qed.
Lemma lem3735163 {_97990 : Type'} : (@ex (_97990 -> Prop)) = (@ex (_97990 -> Prop)).
Proof. exact (eq_refl (@ex (_97990 -> Prop))). Qed.
Lemma lem3735164 {_97990 : Type'} : (term55 _97990) = (term60 _97990).
Proof. exact (MK_COMB (@lem3735163 _97990) (@lem3735162 _97990)). Qed.
Lemma lem3735205 {_97990 : Type'} : (term27 _97990) = (term60 _97990).
Proof. exact (TRANS (@lem3735157 _97990) (@lem3735164 _97990)). Qed.
Lemma lem3735206 {_97990 : Type'} (h1 : term27 _97990) : term60 _97990.
Proof. exact (EQ_MP (@lem3735205 _97990) (@lem3735131 _97990 h1)). Qed.
Lemma lem3735213 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term61 _97990 s t) = (term62 _97990 s t).
Proof. exact (@lem17045 (@FINITE _97990 t) (@SUBSET _97990 s t)). Qed.
Lemma lem3735214 {_97990 : Type'} (s : _97990 -> Prop) : (@FINITE _97990 s) = (@FINITE _97990 s).
Proof. exact (eq_refl (@FINITE _97990 s)). Qed.
Lemma lem3735215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3735216 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term63 _97990 s t) = (term64 _97990 s t).
Proof. exact (MK_COMB (@lem3735215) (@lem3735213 _97990 s t)). Qed.
Lemma lem3735217 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term65 _97990 t s) = (term66 _97990 t s).
Proof. exact (MK_COMB (@lem3735216 _97990 s t) (@lem3735214 _97990 s)). Qed.
Lemma lem3735218 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term37 _97990 t s) = (term65 _97990 t s).
Proof. exact (@lem17265 (term67 _97990 s t) (@FINITE _97990 s)). Qed.
Lemma lem3735219 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term37 _97990 t s) = (term66 _97990 t s).
Proof. exact (TRANS (@lem3735218 _97990 t s) (@lem3735217 _97990 t s)). Qed.
Lemma lem3735220 {_97990 : Type'} (s : _97990 -> Prop) : (term38 _97990 s) = (term68 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735219 _97990 t s)). Qed.
Lemma lem3735221 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735222 {_97990 : Type'} (s : _97990 -> Prop) : (term39 _97990 s) = (term69 _97990 s).
Proof. exact (MK_COMB (@lem3735221 _97990) (@lem3735220 _97990 s)). Qed.
Lemma lem3735223 {_97990 : Type'} : (term40 _97990) = (term70 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735222 _97990 s)). Qed.
Lemma lem3735224 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735225 {_97990 : Type'} : (term28 _97990) = (term71 _97990).
Proof. exact (MK_COMB (@lem3735224 _97990) (@lem3735223 _97990)). Qed.
Lemma lem3735251 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3735252 {_97990 : Type'} (P : type686 _97990) (Q : Prop) : (term74 _97990 P Q) = (term75 _97990 P Q).
Proof. exact (@lem3735251 (_97990 -> Prop) P Q). Qed.
Lemma lem3735253 {_97990 : Type'} (s : _97990 -> Prop) : (term76 _97990 s) = (term77 _97990 s).
Proof. exact (@lem3735252 _97990 (term78 _97990 s) (@FINITE _97990 s)). Qed.
Lemma lem3735254 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term79 _97990 s t) = (term62 _97990 s t).
Proof. exact (eq_refl (term79 _97990 s t)). Qed.
Lemma lem3735255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3735256 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term80 _97990 s t) = (term64 _97990 s t).
Proof. exact (MK_COMB (@lem3735255) (@lem3735254 _97990 s t)). Qed.
Lemma lem3735257 {_97990 : Type'} (s : _97990 -> Prop) : (@FINITE _97990 s) = (@FINITE _97990 s).
Proof. exact (eq_refl (@FINITE _97990 s)). Qed.
Lemma lem3735258 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term81 _97990 t s) = (term66 _97990 t s).
Proof. exact (MK_COMB (@lem3735256 _97990 s t) (@lem3735257 _97990 s)). Qed.
Lemma lem3735259 {_97990 : Type'} (s : _97990 -> Prop) : (term82 _97990 s) = (term68 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735258 _97990 t s)). Qed.
Lemma lem3735260 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735261 {_97990 : Type'} (s : _97990 -> Prop) : (term76 _97990 s) = (term69 _97990 s).
Proof. exact (MK_COMB (@lem3735260 _97990) (@lem3735259 _97990 s)). Qed.
Lemma lem3735262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3735263 {_97990 : Type'} (s : _97990 -> Prop) : (term83 _97990 s) = (term84 _97990 s).
Proof. exact (MK_COMB (@lem3735262) (@lem3735261 _97990 s)). Qed.
Lemma lem3735264 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term79 _97990 s t) = (term62 _97990 s t).
Proof. exact (eq_refl (term79 _97990 s t)). Qed.
Lemma lem3735265 {_97990 : Type'} (s : _97990 -> Prop) : (term85 _97990 s) = (term78 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735264 _97990 s t)). Qed.
Lemma lem3735266 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735267 {_97990 : Type'} (s : _97990 -> Prop) : (term86 _97990 s) = (term87 _97990 s).
Proof. exact (MK_COMB (@lem3735266 _97990) (@lem3735265 _97990 s)). Qed.
Lemma lem3735268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3735269 {_97990 : Type'} (s : _97990 -> Prop) : (term88 _97990 s) = (term89 _97990 s).
Proof. exact (MK_COMB (@lem3735268) (@lem3735267 _97990 s)). Qed.
Lemma lem3735270 {_97990 : Type'} (s : _97990 -> Prop) : (@FINITE _97990 s) = (@FINITE _97990 s).
Proof. exact (eq_refl (@FINITE _97990 s)). Qed.
Lemma lem3735271 {_97990 : Type'} (s : _97990 -> Prop) : (term77 _97990 s) = (term90 _97990 s).
Proof. exact (MK_COMB (@lem3735269 _97990 s) (@lem3735270 _97990 s)). Qed.
Lemma lem3735272 {_97990 : Type'} (s : _97990 -> Prop) : ((term76 _97990 s) = (term77 _97990 s)) = ((term69 _97990 s) = (term90 _97990 s)).
Proof. exact (MK_COMB (@lem3735263 _97990 s) (@lem3735271 _97990 s)). Qed.
Lemma lem3735273 {_97990 : Type'} (s : _97990 -> Prop) : (term69 _97990 s) = (term90 _97990 s).
Proof. exact (EQ_MP (@lem3735272 _97990 s) (@lem3735253 _97990 s)). Qed.
Lemma lem3735322 {_97990 : Type'} : (term70 _97990) = (term91 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735273 _97990 s)). Qed.
Lemma lem3735323 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735358 {_97990 : Type'} : (term71 _97990) = (term92 _97990).
Proof. exact (MK_COMB (@lem3735323 _97990) (@lem3735322 _97990)). Qed.
Lemma lem3735359 {_97990 : Type'} : (term28 _97990) = (term92 _97990).
Proof. exact (TRANS (@lem3735225 _97990) (@lem3735358 _97990)). Qed.
Lemma lem3735360 {_97990 : Type'} (h1 : term28 _97990) : term92 _97990.
Proof. exact (EQ_MP (@lem3735359 _97990) (@lem3735132 _97990 h1)). Qed.
Lemma lem3735361 {_97990 : Type'} (s : _97990 -> Prop) (h1 : term54 _97990 s) : term54 _97990 s.
Proof. exact (h1). Qed.
Lemma lem3735365 {_97990 : Type'} (s : _97990 -> Prop) : (@FINITE _97990 s) = (@FINITE _97990 s).
Proof. exact (eq_refl (@FINITE _97990 s)). Qed.
Lemma lem3735380 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term62 _97990 s t) = (term62 _97990 s t).
Proof. exact (eq_refl (term62 _97990 s t)). Qed.
Lemma lem3735381 {_97990 : Type'} (s : _97990 -> Prop) : (term78 _97990 s) = (term78 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735380 _97990 s t)). Qed.
Lemma lem3735382 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735383 {_97990 : Type'} (s : _97990 -> Prop) : (term87 _97990 s) = (term87 _97990 s).
Proof. exact (MK_COMB (@lem3735382 _97990) (@lem3735381 _97990 s)). Qed.
Lemma lem3735384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3735385 {_97990 : Type'} (s : _97990 -> Prop) : (term89 _97990 s) = (term89 _97990 s).
Proof. exact (MK_COMB (@lem3735384) (@lem3735383 _97990 s)). Qed.
Lemma lem3735386 {_97990 : Type'} (s : _97990 -> Prop) : (term90 _97990 s) = (term90 _97990 s).
Proof. exact (MK_COMB (@lem3735385 _97990 s) (@lem3735365 _97990 s)). Qed.
Lemma lem3735387 {_97990 : Type'} : (term91 _97990) = (term91 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735386 _97990 s)). Qed.
Lemma lem3735388 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735389 {_97990 : Type'} : (term92 _97990) = (term92 _97990).
Proof. exact (MK_COMB (@lem3735388 _97990) (@lem3735387 _97990)). Qed.
Lemma lem3735390 {_97990 : Type'} (h1 : term28 _97990) : term92 _97990.
Proof. exact (EQ_MP (@lem3735389 _97990) (@lem3735360 _97990 h1)). Qed.
Lemma lem3735410 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term44 _97990 s t.
Proof. exact (h1). Qed.
Lemma lem3735412 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term12 _97990 s t.
Proof. exact (proj1 (@lem3735410 _97990 s t h1)). Qed.
Lemma lem3735416 {A : Type'} (P : A -> Prop) (Q : Prop) : (term73 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3735417 {_97990 : Type'} (P : type686 _97990) (Q : Prop) : (term75 _97990 P Q) = (term74 _97990 P Q).
Proof. exact (@lem3735416 (_97990 -> Prop) P Q). Qed.
Lemma lem3735418 {_97990 : Type'} (s : _97990 -> Prop) : (term77 _97990 s) = (term76 _97990 s).
Proof. exact (@lem3735417 _97990 (term78 _97990 s) (@FINITE _97990 s)). Qed.
Lemma lem3735419 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term79 _97990 s t) = (term62 _97990 s t).
Proof. exact (eq_refl (term79 _97990 s t)). Qed.
Lemma lem3735420 {_97990 : Type'} (s : _97990 -> Prop) : (term85 _97990 s) = (term78 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735419 _97990 s t)). Qed.
Lemma lem3735421 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735422 {_97990 : Type'} (s : _97990 -> Prop) : (term86 _97990 s) = (term87 _97990 s).
Proof. exact (MK_COMB (@lem3735421 _97990) (@lem3735420 _97990 s)). Qed.
Lemma lem3735423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3735424 {_97990 : Type'} (s : _97990 -> Prop) : (term88 _97990 s) = (term89 _97990 s).
Proof. exact (MK_COMB (@lem3735423) (@lem3735422 _97990 s)). Qed.
Lemma lem3735425 {_97990 : Type'} (s : _97990 -> Prop) : (@FINITE _97990 s) = (@FINITE _97990 s).
Proof. exact (eq_refl (@FINITE _97990 s)). Qed.
Lemma lem3735426 {_97990 : Type'} (s : _97990 -> Prop) : (term77 _97990 s) = (term90 _97990 s).
Proof. exact (MK_COMB (@lem3735424 _97990 s) (@lem3735425 _97990 s)). Qed.
Lemma lem3735427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3735428 {_97990 : Type'} (s : _97990 -> Prop) : (term93 _97990 s) = (term94 _97990 s).
Proof. exact (MK_COMB (@lem3735427) (@lem3735426 _97990 s)). Qed.
Lemma lem3735429 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term79 _97990 s t) = (term62 _97990 s t).
Proof. exact (eq_refl (term79 _97990 s t)). Qed.
Lemma lem3735430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3735431 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term80 _97990 s t) = (term64 _97990 s t).
Proof. exact (MK_COMB (@lem3735430) (@lem3735429 _97990 s t)). Qed.
Lemma lem3735432 {_97990 : Type'} (s : _97990 -> Prop) : (@FINITE _97990 s) = (@FINITE _97990 s).
Proof. exact (eq_refl (@FINITE _97990 s)). Qed.
Lemma lem3735433 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term81 _97990 t s) = (term66 _97990 t s).
Proof. exact (MK_COMB (@lem3735431 _97990 s t) (@lem3735432 _97990 s)). Qed.
Lemma lem3735434 {_97990 : Type'} (s : _97990 -> Prop) : (term82 _97990 s) = (term68 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735433 _97990 t s)). Qed.
Lemma lem3735435 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735436 {_97990 : Type'} (s : _97990 -> Prop) : (term76 _97990 s) = (term69 _97990 s).
Proof. exact (MK_COMB (@lem3735435 _97990) (@lem3735434 _97990 s)). Qed.
Lemma lem3735437 {_97990 : Type'} (s : _97990 -> Prop) : ((term77 _97990 s) = (term76 _97990 s)) = ((term90 _97990 s) = (term69 _97990 s)).
Proof. exact (MK_COMB (@lem3735428 _97990 s) (@lem3735436 _97990 s)). Qed.
Lemma lem3735438 {_97990 : Type'} (s : _97990 -> Prop) : (term90 _97990 s) = (term69 _97990 s).
Proof. exact (EQ_MP (@lem3735437 _97990 s) (@lem3735418 _97990 s)). Qed.
Lemma lem3735439 {_97990 : Type'} : (term91 _97990) = (term70 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735438 _97990 s)). Qed.
Lemma lem3735440 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735441 {_97990 : Type'} : (term92 _97990) = (term71 _97990).
Proof. exact (MK_COMB (@lem3735440 _97990) (@lem3735439 _97990)). Qed.
Lemma lem3735454 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) : (term66 _97990 t s) = (term66 _97990 t s).
Proof. exact (eq_refl (term66 _97990 t s)). Qed.
Lemma lem3735455 {_97990 : Type'} (s : _97990 -> Prop) : (term68 _97990 s) = (term68 _97990 s).
Proof. exact (fun_ext (fun t : _97990 -> Prop => @lem3735454 _97990 t s)). Qed.
Lemma lem3735456 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735457 {_97990 : Type'} (s : _97990 -> Prop) : (term69 _97990 s) = (term69 _97990 s).
Proof. exact (MK_COMB (@lem3735456 _97990) (@lem3735455 _97990 s)). Qed.
Lemma lem3735458 {_97990 : Type'} : (term70 _97990) = (term70 _97990).
Proof. exact (fun_ext (fun s : _97990 -> Prop => @lem3735457 _97990 s)). Qed.
Lemma lem3735459 {_97990 : Type'} : (@all (_97990 -> Prop)) = (@all (_97990 -> Prop)).
Proof. exact (eq_refl (@all (_97990 -> Prop))). Qed.
Lemma lem3735460 {_97990 : Type'} : (term71 _97990) = (term71 _97990).
Proof. exact (MK_COMB (@lem3735459 _97990) (@lem3735458 _97990)). Qed.
Lemma lem3735461 {_97990 : Type'} : (term92 _97990) = (term71 _97990).
Proof. exact (TRANS (@lem3735441 _97990) (@lem3735460 _97990)). Qed.
Lemma lem3735462 {_97990 : Type'} (h1 : term28 _97990) : term71 _97990.
Proof. exact (EQ_MP (@lem3735461 _97990) (@lem3735390 _97990 h1)). Qed.
Lemma lem3735475 {_97990 : Type'} (_42889 : _97990 -> Prop) (h1 : term28 _97990) : term95 _97990 _42889.
Proof. exact (@lem3735462 _97990 h1 _42889). Qed.
Lemma lem3735476 {_97990 : Type'} (_42889 : _97990 -> Prop) : (term95 _97990 _42889) = (term69 _97990 _42889).
Proof. exact (eq_refl (term95 _97990 _42889)). Qed.
Lemma lem3735477 {_97990 : Type'} (_42889 : _97990 -> Prop) (h1 : term28 _97990) : term69 _97990 _42889.
Proof. exact (EQ_MP (@lem3735476 _97990 _42889) (@lem3735475 _97990 _42889 h1)). Qed.
Lemma lem3735478 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) (h1 : term28 _97990) : term96 _97990 _42889 _42890.
Proof. exact (@lem3735477 _97990 _42889 h1 _42890). Qed.
Lemma lem3735479 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) : (term96 _97990 _42889 _42890) = (term66 _97990 _42890 _42889).
Proof. exact (eq_refl (term96 _97990 _42889 _42890)). Qed.
Lemma lem3735480 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) (h1 : term28 _97990) : term66 _97990 _42890 _42889.
Proof. exact (EQ_MP (@lem3735479 _97990 _42890 _42889) (@lem3735478 _97990 _42889 _42890 h1)). Qed.
Lemma lem3735491 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) : (term66 _97990 _42890 _42889) = (term97 _97990 _42890 _42889).
Proof. exact (@lem3734943 (term8 _97990 _42890) (term98 _97990 _42889 _42890) (@FINITE _97990 _42889)). Qed.
Lemma lem3735492 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) (h1 : term28 _97990) : term97 _97990 _42890 _42889.
Proof. exact (EQ_MP (@lem3735491 _97990 _42890 _42889) (@lem3735480 _97990 _42890 _42889 h1)). Qed.
Lemma lem3735496 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term8 _97990 s.
Proof. exact (proj1 (@lem3735412 _97990 s t h1)). Qed.
Lemma lem3735500 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : @FINITE _97990 t.
Proof. exact (proj2 (@lem3735410 _97990 s t h1)). Qed.
Lemma lem3735501 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term99 _97990 t.
Proof. exact (fun h0 : term8 _97990 t => @lem3735500 _97990 s t h1). Qed.
Lemma lem3735503 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3735504 {_97990 : Type'} (t : _97990 -> Prop) : (term99 _97990 t) = (@FINITE _97990 t).
Proof. exact (@lem3735503 (@FINITE _97990 t)). Qed.
Lemma lem3735505 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : @FINITE _97990 t.
Proof. exact (EQ_MP (@lem3735504 _97990 t) (@lem3735501 _97990 s t h1)). Qed.
Lemma lem3735507 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : @SUBSET _97990 s t.
Proof. exact (proj2 (@lem3735412 _97990 s t h1)). Qed.
Lemma lem3735508 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term101 _97990 s t.
Proof. exact (fun h0 : term98 _97990 s t => @lem3735507 _97990 s t h1). Qed.
Lemma lem3735510 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3735511 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term101 _97990 s t) = (@SUBSET _97990 s t).
Proof. exact (@lem3735510 (@SUBSET _97990 s t)). Qed.
Lemma lem3735512 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : @SUBSET _97990 s t.
Proof. exact (EQ_MP (@lem3735511 _97990 s t) (@lem3735508 _97990 s t h1)). Qed.
Lemma lem3735528 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3735529 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term102 _97990 _42890 _42889) = (term103 _97990 _42889 _42890).
Proof. exact (@lem3735528 (@FINITE _97990 _42889) (term98 _97990 _42889 _42890)). Qed.
Lemma lem3735535 {_97990 : Type'} (_42890 : _97990 -> Prop) : (term104 _97990 _42890) = (term104 _97990 _42890).
Proof. exact (eq_refl (term104 _97990 _42890)). Qed.
Lemma lem3735536 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term97 _97990 _42890 _42889) = (term105 _97990 _42889 _42890).
Proof. exact (MK_COMB (@lem3735535 _97990 _42890) (@lem3735529 _97990 _42889 _42890)). Qed.
Lemma lem3735540 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3735541 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term105 _97990 _42889 _42890) = (term106 _97990 _42889 _42890).
Proof. exact (@lem3735540 (@FINITE _97990 _42889) (term8 _97990 _42890) (term98 _97990 _42889 _42890)). Qed.
Lemma lem3735557 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term97 _97990 _42890 _42889) = (term106 _97990 _42889 _42890).
Proof. exact (TRANS (@lem3735536 _97990 _42889 _42890) (@lem3735541 _97990 _42889 _42890)). Qed.
Lemma lem3735558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3735559 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term107 _97990 _42890 _42889) = (term108 _97990 _42889 _42890).
Proof. exact (MK_COMB (@lem3735558) (@lem3735557 _97990 _42889 _42890)). Qed.
Lemma lem3735575 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term106 _97990 _42889 _42890) = (term106 _97990 _42889 _42890).
Proof. exact (eq_refl (term106 _97990 _42889 _42890)). Qed.
Lemma lem3735576 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : ((term97 _97990 _42890 _42889) = (term106 _97990 _42889 _42890)) = ((term106 _97990 _42889 _42890) = (term106 _97990 _42889 _42890)).
Proof. exact (MK_COMB (@lem3735559 _97990 _42889 _42890) (@lem3735575 _97990 _42889 _42890)). Qed.
Lemma lem3735578 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3735579 (x : Prop) : (x = x) = True.
Proof. exact (@lem3735578 Prop x). Qed.
Lemma lem3735580 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : ((term106 _97990 _42889 _42890) = (term106 _97990 _42889 _42890)) = True.
Proof. exact (@lem3735579 (term106 _97990 _42889 _42890)). Qed.
Lemma lem3735581 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : ((term97 _97990 _42890 _42889) = (term106 _97990 _42889 _42890)) = True.
Proof. exact (TRANS (@lem3735576 _97990 _42889 _42890) (@lem3735580 _97990 _42889 _42890)). Qed.
Lemma lem3735582 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : True = ((term97 _97990 _42890 _42889) = (term106 _97990 _42889 _42890)).
Proof. exact (SYM (@lem3735581 _97990 _42889 _42890)). Qed.
Lemma lem3735583 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term97 _97990 _42890 _42889) = (term106 _97990 _42889 _42890).
Proof. exact (EQ_MP (@lem3735582 _97990 _42889 _42890) (@lem0)). Qed.
Lemma lem3735584 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) (h1 : term28 _97990) : term106 _97990 _42889 _42890.
Proof. exact (EQ_MP (@lem3735583 _97990 _42889 _42890) (@lem3735492 _97990 _42890 _42889 h1)). Qed.
Lemma lem3735586 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3735587 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) : (term106 _97990 _42889 _42890) = (term110 _97990 _42890 _42889).
Proof. exact (@lem3735586 (term62 _97990 _42889 _42890) (@FINITE _97990 _42889)). Qed.
Lemma lem3735589 (a : Prop) (b : Prop) : (term111 a b) = (term112 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3735590 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term113 _97990 _42889 _42890) = (term114 _97990 _42889 _42890).
Proof. exact (@lem3735589 (term8 _97990 _42890) (term98 _97990 _42889 _42890)). Qed.
Lemma lem3735592 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3735593 {_97990 : Type'} (_42890 : _97990 -> Prop) : (term41 _97990 _42890) = (@FINITE _97990 _42890).
Proof. exact (@lem3735592 (@FINITE _97990 _42890)). Qed.
Lemma lem3735594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3735595 {_97990 : Type'} (_42890 : _97990 -> Prop) : (term116 _97990 _42890) = (term117 _97990 _42890).
Proof. exact (MK_COMB (@lem3735594) (@lem3735593 _97990 _42890)). Qed.
Lemma lem3735597 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3735598 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term118 _97990 _42889 _42890) = (@SUBSET _97990 _42889 _42890).
Proof. exact (@lem3735597 (@SUBSET _97990 _42889 _42890)). Qed.
Lemma lem3735599 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term114 _97990 _42889 _42890) = (term67 _97990 _42889 _42890).
Proof. exact (MK_COMB (@lem3735595 _97990 _42890) (@lem3735598 _97990 _42889 _42890)). Qed.
Lemma lem3735600 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term113 _97990 _42889 _42890) = (term67 _97990 _42889 _42890).
Proof. exact (TRANS (@lem3735590 _97990 _42889 _42890) (@lem3735599 _97990 _42889 _42890)). Qed.
Lemma lem3735601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3735602 {_97990 : Type'} (_42889 : _97990 -> Prop) (_42890 : _97990 -> Prop) : (term119 _97990 _42889 _42890) = (term120 _97990 _42889 _42890).
Proof. exact (MK_COMB (@lem3735601) (@lem3735600 _97990 _42889 _42890)). Qed.
Lemma lem3735603 {_97990 : Type'} (_42889 : _97990 -> Prop) : (@FINITE _97990 _42889) = (@FINITE _97990 _42889).
Proof. exact (eq_refl (@FINITE _97990 _42889)). Qed.
Lemma lem3735604 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) : (term110 _97990 _42890 _42889) = (term37 _97990 _42890 _42889).
Proof. exact (MK_COMB (@lem3735602 _97990 _42889 _42890) (@lem3735603 _97990 _42889)). Qed.
Lemma lem3735605 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) : (term106 _97990 _42889 _42890) = (term37 _97990 _42890 _42889).
Proof. exact (TRANS (@lem3735587 _97990 _42890 _42889) (@lem3735604 _97990 _42890 _42889)). Qed.
Lemma lem3735607 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term67 _97990 s t.
Proof. exact (conj (@lem3735505 _97990 s t h1) (@lem3735512 _97990 s t h1)). Qed.
Lemma lem3735609 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) (h1 : term28 _97990) : term37 _97990 _42890 _42889.
Proof. exact (EQ_MP (@lem3735605 _97990 _42890 _42889) (@lem3735584 _97990 _42889 _42890 h1)). Qed.
Lemma lem3735610 {_97990 : Type'} (_42890 : _97990 -> Prop) (_42889 : _97990 -> Prop) (h1 : term28 _97990) : term37 _97990 _42890 _42889.
Proof. exact (@lem3735609 _97990 _42890 _42889 h1). Qed.
Lemma lem3735611 {_97990 : Type'} (t : _97990 -> Prop) (s : _97990 -> Prop) (h1 : term28 _97990) : term37 _97990 t s.
Proof. exact (@lem3735610 _97990 t s h1). Qed.
Lemma lem3735614 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : @FINITE _97990 s.
Proof. exact (@lem3735611 _97990 t s h1 (@lem3735607 _97990 s t h2)). Qed.
Lemma lem3735615 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : term99 _97990 s.
Proof. exact (fun h0 : term8 _97990 s => @lem3735614 _97990 s t h1 h2). Qed.
Lemma lem3735617 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3735618 {_97990 : Type'} (s : _97990 -> Prop) : (term99 _97990 s) = (@FINITE _97990 s).
Proof. exact (@lem3735617 (@FINITE _97990 s)). Qed.
Lemma lem3735619 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : @FINITE _97990 s.
Proof. exact (EQ_MP (@lem3735618 _97990 s) (@lem3735615 _97990 s t h1 h2)). Qed.
Lemma lem3735622 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3735624 {_97990 : Type'} (s : _97990 -> Prop) : (term8 _97990 s) = (term121 _97990 s).
Proof. exact (@lem3735622 (@FINITE _97990 s)). Qed.
Lemma lem3735627 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term44 _97990 s t) : term121 _97990 s.
Proof. exact (EQ_MP (@lem3735624 _97990 s) (@lem3735496 _97990 s t h1)). Qed.
Lemma lem3735630 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : False.
Proof. exact (@lem3735627 _97990 s t h2 (@lem3735619 _97990 s t h1 h2)). Qed.
Lemma lem3735631 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : term122.
Proof. exact (fun h0 : ~ False => @lem3735630 _97990 s t h1 h2). Qed.
Lemma lem3735633 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3735634 : term122 = False.
Proof. exact (@lem3735633 False). Qed.
Lemma lem3735635 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : False.
Proof. exact (EQ_MP (@lem3735634) (@lem3735631 _97990 s t h1 h2)). Qed.
Lemma lem3735636 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : (term44 _97990 s t) = False.
Proof. exact (prop_ext (fun h3 : term44 _97990 s t => @lem3735635 _97990 s t h1 h2) (fun h3 : False => @lem3735410 _97990 s t h2)). Qed.
Lemma lem3735637 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term28 _97990) (h2 : term44 _97990 s t) : False.
Proof. exact (EQ_MP (@lem3735636 _97990 s t h1 h2) (@lem3735410 _97990 s t h2)). Qed.
Lemma lem3735638 {_97990 : Type'} (s : _97990 -> Prop) (h1 : term28 _97990) (h2 : term54 _97990 s) : False.
Proof. exact (ex_elim (@lem3735361 _97990 s h2) (fun t : _97990 -> Prop => fun h0 : term53 _97990 s t => @lem3735637 _97990 s t h1 h0)). Qed.
Lemma lem3735639 {_97990 : Type'} (h1 : term28 _97990) (h2 : term27 _97990) : False.
Proof. exact (ex_elim (@lem3735206 _97990 h2) (fun s : _97990 -> Prop => fun h0 : term59 _97990 s => @lem3735638 _97990 s h1 h0)). Qed.
Lemma lem3735640 {_97990 : Type'} (h1 : term27 _97990) : term33 _97990.
Proof. exact (fun h0 : term28 _97990 => @lem3735639 _97990 h0 h1). Qed.
Lemma lem3735641 {_97990 : Type'} : (term33 _97990) = (term34 _97990).
Proof. exact (@lem69 (term28 _97990)). Qed.
Lemma lem3735642 {_97990 : Type'} (h1 : term27 _97990) : term34 _97990.
Proof. exact (EQ_MP (@lem3735641 _97990) (@lem3735640 _97990 h1)). Qed.
Lemma lem3735643 {_97990 : Type'} : term36 _97990.
Proof. exact (fun h0 : term27 _97990 => @lem3735642 _97990 h0). Qed.
Lemma lem3735644 {_97990 : Type'} : term29 _97990.
Proof. exact (EQ_MP (@lem3735130 _97990) (@lem3735643 _97990)). Qed.
Lemma lem3735646 {_97990 : Type'} : term29 _97990.
Proof. exact (@lem3735014 _97990 (@lem3735644 _97990)). Qed.
Lemma lem3735647 {_97990 : Type'} (h1 : term27 _97990) : term33 _97990.
Proof. exact (@lem3735646 _97990 (@lem3734996 _97990 h1)). Qed.
Lemma lem3735648 {_97990 : Type'} (h1 : term27 _97990) : False.
Proof. exact (@lem3735647 _97990 h1 (@lem3734997 _97990)). Qed.
Lemma lem3735649 {_97990 : Type'} (h1 : term27 _97990) : (term27 _97990) = False.
Proof. exact (prop_ext (fun h2 : term27 _97990 => @lem3735648 _97990 h1) (fun h2 : False => @lem3734996 _97990 h1)). Qed.
Lemma lem3735650 {_97990 : Type'} (h1 : term27 _97990) : False.
Proof. exact (EQ_MP (@lem3735649 _97990 h1) (@lem3734996 _97990 h1)). Qed.
Lemma lem3735651 {_97990 : Type'} : term26 _97990.
Proof. exact (fun h0 : term27 _97990 => @lem3735650 _97990 h0). Qed.
Lemma lem3735652 {_97990 : Type'} : term24 _97990.
Proof. exact (EQ_MP (@lem3734995 _97990) (@lem3735651 _97990)). Qed.
Lemma lem3735653 {_97990 : Type'} : term23 _97990.
Proof. exact (EQ_MP (@lem3734991 _97990) (@lem3735652 _97990)). Qed.
