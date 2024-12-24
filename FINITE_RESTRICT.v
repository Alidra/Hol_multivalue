Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RESTRICT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import SUBSET_RESTRICT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Lemma lem3599925 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3599926 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3599927 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3599926 t1) (@lem3599925 t1)). Qed.
Lemma lem3599928 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3599927 t1 t2). Qed.
Lemma lem3599929 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3599930 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3599929 t1 t2) (@lem3599928 t1 t2)). Qed.
Lemma lem3599931 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3599930 t1 t2 t3). Qed.
Lemma lem3599932 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3599933 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3599932 t1 t2 t3) (@lem3599931 t1 t2 t3)). Qed.
Lemma lem3599934 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3599933 t1 t2 t3)). Qed.
Lemma lem3599936 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3599937 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem3599936 (term8 A)). Qed.
Lemma lem3599938 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3599937 A)). Qed.
Lemma lem3599939 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3599940 {A : Type'} : term11 A.
Proof. exact (@lem3221162 A). Qed.
Lemma lem3599944 {A : Type'} : term12 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem3599946 {_84465 : Type'} : term12 _84465.
Proof. exact (@lem3599924 _84465). Qed.
Lemma lem3599949 {_84465 A : Type'} (h1 : term13 _84465 A) : term13 _84465 A.
Proof. exact (h1). Qed.
Lemma lem3599950 {_84465 A : Type'} : term14 _84465 A.
Proof. exact (fun h0 : term13 _84465 A => @lem3599949 _84465 A h0). Qed.
Lemma lem3599951 {_84465 A : Type'} (h1 : term14 _84465 A) : term14 _84465 A.
Proof. exact (h1). Qed.
Lemma lem3599952 {_84465 A : Type'} (h1 : term13 _84465 A) : term13 _84465 A.
Proof. exact (h1). Qed.
Lemma lem3599953 {_84465 A : Type'} (h1 : term13 _84465 A) (h2 : term14 _84465 A) : term13 _84465 A.
Proof. exact (@lem3599951 _84465 A h2 (@lem3599952 _84465 A h1)). Qed.
Lemma lem3599954 {_84465 A : Type'} (h1 : term13 _84465 A) : term15 _84465 A.
Proof. exact (fun h0 : term14 _84465 A => @lem3599953 _84465 A h1 h0). Qed.
Lemma lem3599955 {_84465 A : Type'} (h1 : term14 _84465 A) : term14 _84465 A.
Proof. exact (h1). Qed.
Lemma lem3599956 {_84465 A : Type'} (h1 : term13 _84465 A) (h2 : term14 _84465 A) : term13 _84465 A.
Proof. exact (@lem3599954 _84465 A h1 (@lem3599955 _84465 A h2)). Qed.
Lemma lem3599957 {_84465 A : Type'} (h1 : term14 _84465 A) : term14 _84465 A.
Proof. exact (fun h0 : term13 _84465 A => @lem3599956 _84465 A h0 h1). Qed.
Lemma lem3599958 {_84465 A : Type'} : term16 _84465 A.
Proof. exact (fun h0 : term14 _84465 A => @lem3599957 _84465 A h0). Qed.
Lemma lem3599961 {_84465 A : Type'} : term14 _84465 A.
Proof. exact (@lem3599958 _84465 A (@lem3599950 _84465 A)). Qed.
Lemma lem3599962 {_84465 A : Type'} : term14 _84465 A.
Proof. exact (@lem3599961 _84465 A). Qed.
Lemma lem3600026 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3600027 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem3600026 (term11 A)). Qed.
Lemma lem3600042 {_84465 : Type'} : (term19 _84465) = (term19 _84465).
Proof. exact (eq_refl (term19 _84465)). Qed.
Lemma lem3600043 {_84465 A : Type'} : (term20 _84465 A) = (term21 _84465 A).
Proof. exact (MK_COMB (@lem3600042 _84465) (@lem3600027 A)). Qed.
Lemma lem3600046 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem3600047 {_84465 A : Type'} : (term23 _84465 A) = (term24 _84465 A).
Proof. exact (MK_COMB (@lem3600046 A) (@lem3600043 _84465 A)). Qed.
Lemma lem3600050 {_84465 : Type'} : (term22 _84465) = (term22 _84465).
Proof. exact (eq_refl (term22 _84465)). Qed.
Lemma lem3600051 {_84465 A : Type'} : (term25 _84465 A) = (term26 _84465 A).
Proof. exact (MK_COMB (@lem3600050 _84465) (@lem3600047 _84465 A)). Qed.
Lemma lem3600054 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem3600059 {_84465 A : Type'} : (term13 _84465 A) = (term28 _84465 A).
Proof. exact (MK_COMB (@lem3600054 A) (@lem3600051 _84465 A)). Qed.
Lemma lem3600060 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : _39018 = (term29 A).
Proof. exact (h1). Qed.
Lemma lem3600061 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3600062 {A : Type'} (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (_39018 s) = (term30 A s).
Proof. exact (MK_COMB (@lem3600060 A _39018 h1) (@lem3600061 A s)). Qed.
Lemma lem3600063 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem3600064 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term32 A _39018 s) = (term32 A _39018 s).
Proof. exact (eq_refl (term32 A _39018 s)). Qed.
Lemma lem3600065 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((_39018 s) = (term30 A s)) = ((_39018 s) = (term31 A s)).
Proof. exact (MK_COMB (@lem3600064 A _39018 s) (@lem3600063 A s)). Qed.
Lemma lem3600066 {A : Type'} (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (_39018 s) = (term31 A s).
Proof. exact (EQ_MP (@lem3600065 A _39018 s) (@lem3600062 A s _39018 h1)). Qed.
Lemma lem3600067 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3600068 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (_39018 s P) = (term33 A s P).
Proof. exact (MK_COMB (@lem3600066 A s _39018 h1) (@lem3600067 A P)). Qed.
Lemma lem3600069 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term33 A s P) = (term34 A s P).
Proof. exact (eq_refl (term33 A s P)). Qed.
Lemma lem3600070 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term35 A _39018 s P) = (term35 A _39018 s P).
Proof. exact (eq_refl (term35 A _39018 s P)). Qed.
Lemma lem3600071 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P) = (term33 A s P)) = ((_39018 s P) = (term34 A s P)).
Proof. exact (MK_COMB (@lem3600070 A _39018 s P) (@lem3600069 A s P)). Qed.
Lemma lem3600072 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (_39018 s P) = (term34 A s P).
Proof. exact (EQ_MP (@lem3600071 A _39018 s P) (@lem3600068 A s P _39018 h1)). Qed.
Lemma lem3600074 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3600076 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term34 A s P) = (_39018 s P).
Proof. exact (SYM (@lem3600072 A s P _39018 h1)). Qed.
Lemma lem3600077 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term34 A s P) = (_39018 s P).
Proof. exact (@lem3600076 A s P _39018 h1). Qed.
Lemma lem3600078 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3600079 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term36 A s P) = (term37 A _39018 s P).
Proof. exact (MK_COMB (@lem3600078 A) (@lem3600077 A s P _39018 h1)). Qed.
Lemma lem3600080 {A : Type'} : (@SUBSET A) = (@SUBSET A).
Proof. exact (eq_refl (@SUBSET A)). Qed.
Lemma lem3600081 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term38 A s P) = (term39 A _39018 s P).
Proof. exact (MK_COMB (@lem3600080 A) (@lem3600079 A s P _39018 h1)). Qed.
Lemma lem3600082 {A : Type'} (P : A -> Prop) (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term40 A P s) = (term41 A _39018 P s).
Proof. exact (MK_COMB (@lem3600081 A s P _39018 h1) (@lem3600074 A s)). Qed.
Lemma lem3600083 {A : Type'} (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term42 A s) = (term43 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600082 A P s _39018 h1)). Qed.
Lemma lem3600084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600085 {A : Type'} (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term44 A s) = (term45 A _39018 s).
Proof. exact (MK_COMB (@lem3600084 A) (@lem3600083 A s _39018 h1)). Qed.
Lemma lem3600086 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term46 A) = (term47 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600085 A s _39018 h1)). Qed.
Lemma lem3600087 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600088 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term11 A) = (term48 A _39018).
Proof. exact (MK_COMB (@lem3600087 A) (@lem3600086 A _39018 h1)). Qed.
Lemma lem3600089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600090 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term18 A) = (term49 A _39018).
Proof. exact (MK_COMB (@lem3600089) (@lem3600088 A _39018 h1)). Qed.
Lemma lem3600091 {_84465 : Type'} (s : _84465 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3600111 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term50 _84465 GEN_PVAR_11 s P x) = (term50 _84465 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term50 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600112 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term51 _84465 GEN_PVAR_11 s P) = (term51 _84465 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3600111 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600113 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3600114 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term52 _84465 GEN_PVAR_11 s P) = (term52 _84465 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600113 _84465) (@lem3600112 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600115 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term34 _84465 s P) = (term34 _84465 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600114 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600116 {_84465 : Type'} : (@GSPEC _84465) = (@GSPEC _84465).
Proof. exact (eq_refl (@GSPEC _84465)). Qed.
Lemma lem3600117 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term36 _84465 s P) = (term36 _84465 s P).
Proof. exact (MK_COMB (@lem3600116 _84465) (@lem3600115 _84465 s P)). Qed.
Lemma lem3600118 {_84465 : Type'} : (@SUBSET _84465) = (@SUBSET _84465).
Proof. exact (eq_refl (@SUBSET _84465)). Qed.
Lemma lem3600119 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term38 _84465 s P) = (term38 _84465 s P).
Proof. exact (MK_COMB (@lem3600118 _84465) (@lem3600117 _84465 s P)). Qed.
Lemma lem3600120 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term40 _84465 P s) = (term40 _84465 P s).
Proof. exact (MK_COMB (@lem3600119 _84465 s P) (@lem3600091 _84465 s)). Qed.
Lemma lem3600121 {_84465 : Type'} (s : _84465 -> Prop) : (term42 _84465 s) = (term42 _84465 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600120 _84465 P s)). Qed.
Lemma lem3600122 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600123 {_84465 : Type'} (s : _84465 -> Prop) : (term44 _84465 s) = (term44 _84465 s).
Proof. exact (MK_COMB (@lem3600122 _84465) (@lem3600121 _84465 s)). Qed.
Lemma lem3600124 {_84465 : Type'} : (term46 _84465) = (term46 _84465).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600123 _84465 s)). Qed.
Lemma lem3600125 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600126 {_84465 : Type'} : (term11 _84465) = (term11 _84465).
Proof. exact (MK_COMB (@lem3600125 _84465) (@lem3600124 _84465)). Qed.
Lemma lem3600127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600128 {_84465 : Type'} : (term19 _84465) = (term19 _84465).
Proof. exact (MK_COMB (@lem3600127) (@lem3600126 _84465)). Qed.
Lemma lem3600129 {_84465 A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term21 _84465 A) = (term53 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600128 _84465) (@lem3600090 A _39018 h1)). Qed.
Lemma lem3600146 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term54 A t s).
Proof. exact (eq_refl (term54 A t s)). Qed.
Lemma lem3600147 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3600146 A t s)). Qed.
Lemma lem3600148 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600149 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3600148 A) (@lem3600147 A s)). Qed.
Lemma lem3600150 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600149 A s)). Qed.
Lemma lem3600151 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600152 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3600151 A) (@lem3600150 A)). Qed.
Lemma lem3600153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600154 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3600153) (@lem3600152 A)). Qed.
Lemma lem3600155 {_84465 A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term24 _84465 A) = (term58 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600154 A) (@lem3600129 _84465 A _39018 h1)). Qed.
Lemma lem3600172 {_84465 : Type'} (t : _84465 -> Prop) (s : _84465 -> Prop) : (term54 _84465 t s) = (term54 _84465 t s).
Proof. exact (eq_refl (term54 _84465 t s)). Qed.
Lemma lem3600173 {_84465 : Type'} (s : _84465 -> Prop) : (term55 _84465 s) = (term55 _84465 s).
Proof. exact (fun_ext (fun t : _84465 -> Prop => @lem3600172 _84465 t s)). Qed.
Lemma lem3600174 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600175 {_84465 : Type'} (s : _84465 -> Prop) : (term56 _84465 s) = (term56 _84465 s).
Proof. exact (MK_COMB (@lem3600174 _84465) (@lem3600173 _84465 s)). Qed.
Lemma lem3600176 {_84465 : Type'} : (term57 _84465) = (term57 _84465).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600175 _84465 s)). Qed.
Lemma lem3600177 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600178 {_84465 : Type'} : (term12 _84465) = (term12 _84465).
Proof. exact (MK_COMB (@lem3600177 _84465) (@lem3600176 _84465)). Qed.
Lemma lem3600179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600180 {_84465 : Type'} : (term22 _84465) = (term22 _84465).
Proof. exact (MK_COMB (@lem3600179) (@lem3600178 _84465)). Qed.
Lemma lem3600181 {_84465 A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term26 _84465 A) = (term59 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600180 _84465) (@lem3600155 _84465 A _39018 h1)). Qed.
Lemma lem3600183 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term34 A s P) = (_39018 s P).
Proof. exact (SYM (@lem3600072 A s P _39018 h1)). Qed.
Lemma lem3600184 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term34 A s P) = (_39018 s P).
Proof. exact (@lem3600183 A s P _39018 h1). Qed.
Lemma lem3600185 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3600186 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term36 A s P) = (term37 A _39018 s P).
Proof. exact (MK_COMB (@lem3600185 A) (@lem3600184 A s P _39018 h1)). Qed.
Lemma lem3600187 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3600188 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term60 A s P) = (term61 A _39018 s P).
Proof. exact (MK_COMB (@lem3600187 A) (@lem3600186 A s P _39018 h1)). Qed.
Lemma lem3600193 {A : Type'} (s : A -> Prop) : (term62 A s) = (term62 A s).
Proof. exact (eq_refl (term62 A s)). Qed.
Lemma lem3600194 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term63 A s P) = (term64 A _39018 s P).
Proof. exact (MK_COMB (@lem3600193 A s) (@lem3600188 A s P _39018 h1)). Qed.
Lemma lem3600195 {A : Type'} (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term65 A s) = (term66 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600194 A s P _39018 h1)). Qed.
Lemma lem3600196 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600197 {A : Type'} (s : A -> Prop) (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term67 A s) = (term68 A _39018 s).
Proof. exact (MK_COMB (@lem3600196 A) (@lem3600195 A s _39018 h1)). Qed.
Lemma lem3600198 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term69 A) = (term70 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600197 A s _39018 h1)). Qed.
Lemma lem3600199 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600200 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term8 A) = (term71 A _39018).
Proof. exact (MK_COMB (@lem3600199 A) (@lem3600198 A _39018 h1)). Qed.
Lemma lem3600201 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600202 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term10 A) = (term72 A _39018).
Proof. exact (MK_COMB (@lem3600201) (@lem3600200 A _39018 h1)). Qed.
Lemma lem3600203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600204 {A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term27 A) = (term73 A _39018).
Proof. exact (MK_COMB (@lem3600203) (@lem3600202 A _39018 h1)). Qed.
Lemma lem3600205 {_84465 A : Type'} (_39018 : type636 A) (h1 : _39018 = (term29 A)) : (term28 _84465 A) = (term74 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600204 A _39018 h1) (@lem3600181 _84465 A _39018 h1)). Qed.
Lemma lem3600206 {_84465 A : Type'} (_39018 : type636 A) : term75 _84465 A _39018.
Proof. exact (fun h0 : _39018 = (term29 A) => @lem3600205 _84465 A _39018 h0). Qed.
Lemma lem3600207 {_84465 A : Type'} : term76 _84465 A.
Proof. exact (fun _39018 : type636 A => @lem3600206 _84465 A _39018). Qed.
Lemma lem3600209 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term77 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem3600210 {A : Type'} (P : Prop) (c : type636 A) (Q : type138 A) : term78 A P c Q.
Proof. exact (@lem3600209 (type636 A) P c Q). Qed.
Lemma lem3600211 {_84465 A : Type'} : term79 _84465 A.
Proof. exact (@lem3600210 A (term28 _84465 A) (term29 A) (term80 _84465 A)). Qed.
Lemma lem3600212 {_84465 A : Type'} (_39018 : type636 A) : (term81 _84465 A _39018) = (term74 _84465 A _39018).
Proof. exact (eq_refl (term81 _84465 A _39018)). Qed.
Lemma lem3600213 {_84465 A : Type'} : (term82 _84465 A) = (term82 _84465 A).
Proof. exact (eq_refl (term82 _84465 A)). Qed.
Lemma lem3600214 {_84465 A : Type'} (_39018 : type636 A) : ((term28 _84465 A) = (term81 _84465 A _39018)) = ((term28 _84465 A) = (term74 _84465 A _39018)).
Proof. exact (MK_COMB (@lem3600213 _84465 A) (@lem3600212 _84465 A _39018)). Qed.
Lemma lem3600215 {A : Type'} (_39018 : type636 A) : (term83 A _39018) = (term83 A _39018).
Proof. exact (eq_refl (term83 A _39018)). Qed.
Lemma lem3600216 {_84465 A : Type'} (_39018 : type636 A) : (term84 _84465 A _39018) = (term75 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600215 A _39018) (@lem3600214 _84465 A _39018)). Qed.
Lemma lem3600217 {_84465 A : Type'} : (term85 _84465 A) = (term86 _84465 A).
Proof. exact (fun_ext (fun _39018 : type636 A => @lem3600216 _84465 A _39018)). Qed.
Lemma lem3600218 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3600219 {_84465 A : Type'} : (term87 _84465 A) = (term76 _84465 A).
Proof. exact (MK_COMB (@lem3600218 A) (@lem3600217 _84465 A)). Qed.
Lemma lem3600220 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600221 {_84465 A : Type'} : (term88 _84465 A) = (term89 _84465 A).
Proof. exact (MK_COMB (@lem3600220) (@lem3600219 _84465 A)). Qed.
Lemma lem3600222 {_84465 A : Type'} (_39018 : type636 A) : (term81 _84465 A _39018) = (term74 _84465 A _39018).
Proof. exact (eq_refl (term81 _84465 A _39018)). Qed.
Lemma lem3600223 {A : Type'} (_39018 : type636 A) : (term83 A _39018) = (term83 A _39018).
Proof. exact (eq_refl (term83 A _39018)). Qed.
Lemma lem3600224 {_84465 A : Type'} (_39018 : type636 A) : (term90 _84465 A _39018) = (term91 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600223 A _39018) (@lem3600222 _84465 A _39018)). Qed.
Lemma lem3600225 {_84465 A : Type'} : (term92 _84465 A) = (term93 _84465 A).
Proof. exact (fun_ext (fun _39018 : type636 A => @lem3600224 _84465 A _39018)). Qed.
Lemma lem3600226 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3600227 {_84465 A : Type'} : (term94 _84465 A) = (term95 _84465 A).
Proof. exact (MK_COMB (@lem3600226 A) (@lem3600225 _84465 A)). Qed.
Lemma lem3600228 {_84465 A : Type'} : (term82 _84465 A) = (term82 _84465 A).
Proof. exact (eq_refl (term82 _84465 A)). Qed.
Lemma lem3600229 {_84465 A : Type'} : ((term28 _84465 A) = (term94 _84465 A)) = ((term28 _84465 A) = (term95 _84465 A)).
Proof. exact (MK_COMB (@lem3600228 _84465 A) (@lem3600227 _84465 A)). Qed.
Lemma lem3600230 {_84465 A : Type'} : (term79 _84465 A) = (term96 _84465 A).
Proof. exact (MK_COMB (@lem3600221 _84465 A) (@lem3600229 _84465 A)). Qed.
Lemma lem3600231 {_84465 A : Type'} : term96 _84465 A.
Proof. exact (EQ_MP (@lem3600230 _84465 A) (@lem3600211 _84465 A)). Qed.
Lemma lem3600232 {_84465 A : Type'} : (term28 _84465 A) = (term95 _84465 A).
Proof. exact (@lem3600231 _84465 A (@lem3600207 _84465 A)). Qed.
Lemma lem3600234 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term97 _3571 _3575 t)) = (term98 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem3600235 {A : Type'} (s : type636 A) (t : type636 A) : (s = (term99 A t)) = (term100 A s t).
Proof. exact (@lem3600234 (type672 A) (A -> Prop) s t). Qed.
Lemma lem3600236 {A : Type'} (_39018 : type636 A) : (_39018 = (term101 A)) = (term102 A _39018).
Proof. exact (@lem3600235 A _39018 (term29 A)). Qed.
Lemma lem3600237 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem3600238 {A : Type'} : (term101 A) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600237 A s)). Qed.
Lemma lem3600239 {A : Type'} (_39018 : type636 A) : (@eq ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018) = (@eq ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018)). Qed.
Lemma lem3600240 {A : Type'} (_39018 : type636 A) : (_39018 = (term101 A)) = (_39018 = (term29 A)).
Proof. exact (MK_COMB (@lem3600239 A _39018) (@lem3600238 A)). Qed.
Lemma lem3600241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600242 {A : Type'} (_39018 : type636 A) : (term103 A _39018) = (term104 A _39018).
Proof. exact (MK_COMB (@lem3600241) (@lem3600240 A _39018)). Qed.
Lemma lem3600243 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem3600244 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term32 A _39018 s) = (term32 A _39018 s).
Proof. exact (eq_refl (term32 A _39018 s)). Qed.
Lemma lem3600245 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((_39018 s) = (term30 A s)) = ((_39018 s) = (term31 A s)).
Proof. exact (MK_COMB (@lem3600244 A _39018 s) (@lem3600243 A s)). Qed.
Lemma lem3600246 {A : Type'} (_39018 : type636 A) : (term105 A _39018) = (term106 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600245 A _39018 s)). Qed.
Lemma lem3600247 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600248 {A : Type'} (_39018 : type636 A) : (term102 A _39018) = (term107 A _39018).
Proof. exact (MK_COMB (@lem3600247 A) (@lem3600246 A _39018)). Qed.
Lemma lem3600249 {A : Type'} (_39018 : type636 A) : ((_39018 = (term101 A)) = (term102 A _39018)) = ((_39018 = (term29 A)) = (term107 A _39018)).
Proof. exact (MK_COMB (@lem3600242 A _39018) (@lem3600248 A _39018)). Qed.
Lemma lem3600250 {A : Type'} (_39018 : type636 A) : (_39018 = (term29 A)) = (term107 A _39018).
Proof. exact (EQ_MP (@lem3600249 A _39018) (@lem3600236 A _39018)). Qed.
Lemma lem3600252 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term97 _3571 _3575 t)) = (term98 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem3600253 {A : Type'} (s : type672 A) (t : type672 A) : (s = (term108 A t)) = (term109 A s t).
Proof. exact (@lem3600252 (A -> Prop) (A -> Prop) s t). Qed.
Lemma lem3600254 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((_39018 s) = (term110 A s)) = (term111 A _39018 s).
Proof. exact (@lem3600253 A (_39018 s) (term31 A s)). Qed.
Lemma lem3600255 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term33 A s P) = (term34 A s P).
Proof. exact (eq_refl (term33 A s P)). Qed.
Lemma lem3600256 {A : Type'} (s : A -> Prop) : (term110 A s) = (term31 A s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600255 A s P)). Qed.
Lemma lem3600257 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term32 A _39018 s) = (term32 A _39018 s).
Proof. exact (eq_refl (term32 A _39018 s)). Qed.
Lemma lem3600258 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((_39018 s) = (term110 A s)) = ((_39018 s) = (term31 A s)).
Proof. exact (MK_COMB (@lem3600257 A _39018 s) (@lem3600256 A s)). Qed.
Lemma lem3600259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600260 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term112 A _39018 s) = (term113 A _39018 s).
Proof. exact (MK_COMB (@lem3600259) (@lem3600258 A _39018 s)). Qed.
Lemma lem3600261 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term33 A s P) = (term34 A s P).
Proof. exact (eq_refl (term33 A s P)). Qed.
Lemma lem3600262 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term35 A _39018 s P) = (term35 A _39018 s P).
Proof. exact (eq_refl (term35 A _39018 s P)). Qed.
Lemma lem3600263 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P) = (term33 A s P)) = ((_39018 s P) = (term34 A s P)).
Proof. exact (MK_COMB (@lem3600262 A _39018 s P) (@lem3600261 A s P)). Qed.
Lemma lem3600264 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term114 A _39018 s) = (term115 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600263 A _39018 s P)). Qed.
Lemma lem3600265 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600266 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term111 A _39018 s) = (term116 A _39018 s).
Proof. exact (MK_COMB (@lem3600265 A) (@lem3600264 A _39018 s)). Qed.
Lemma lem3600267 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (((_39018 s) = (term110 A s)) = (term111 A _39018 s)) = (((_39018 s) = (term31 A s)) = (term116 A _39018 s)).
Proof. exact (MK_COMB (@lem3600260 A _39018 s) (@lem3600266 A _39018 s)). Qed.
Lemma lem3600268 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((_39018 s) = (term31 A s)) = (term116 A _39018 s).
Proof. exact (EQ_MP (@lem3600267 A _39018 s) (@lem3600254 A _39018 s)). Qed.
Lemma lem3600270 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term97 _3571 _3575 t)) = (term98 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem3600271 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term117 A t)) = (term118 A s t).
Proof. exact (@lem3600270 Prop A s t). Qed.
Lemma lem3600272 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P) = (term119 A s P)) = (term120 A _39018 s P).
Proof. exact (@lem3600271 A (_39018 s P) (term34 A s P)). Qed.
Lemma lem3600273 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term121 A s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P).
Proof. exact (eq_refl (term121 A s P GEN_PVAR_91)). Qed.
Lemma lem3600274 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term119 A s P) = (term34 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3600273 A GEN_PVAR_91 s P)). Qed.
Lemma lem3600275 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term35 A _39018 s P) = (term35 A _39018 s P).
Proof. exact (eq_refl (term35 A _39018 s P)). Qed.
Lemma lem3600276 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P) = (term119 A s P)) = ((_39018 s P) = (term34 A s P)).
Proof. exact (MK_COMB (@lem3600275 A _39018 s P) (@lem3600274 A s P)). Qed.
Lemma lem3600277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600278 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term122 A _39018 s P) = (term123 A _39018 s P).
Proof. exact (MK_COMB (@lem3600277) (@lem3600276 A _39018 s P)). Qed.
Lemma lem3600279 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term121 A s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P).
Proof. exact (eq_refl (term121 A s P GEN_PVAR_91)). Qed.
Lemma lem3600280 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term124 A _39018 s P GEN_PVAR_91) = (term124 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term124 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3600281 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P GEN_PVAR_91) = (term121 A s P GEN_PVAR_91)) = ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)).
Proof. exact (MK_COMB (@lem3600280 A _39018 s P GEN_PVAR_91) (@lem3600279 A GEN_PVAR_91 s P)). Qed.
Lemma lem3600282 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term125 A _39018 s P) = (term126 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3600281 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3600283 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3600284 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term120 A _39018 s P) = (term127 A _39018 s P).
Proof. exact (MK_COMB (@lem3600283 A) (@lem3600282 A _39018 s P)). Qed.
Lemma lem3600285 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (((_39018 s P) = (term119 A s P)) = (term120 A _39018 s P)) = (((_39018 s P) = (term34 A s P)) = (term127 A _39018 s P)).
Proof. exact (MK_COMB (@lem3600278 A _39018 s P) (@lem3600284 A _39018 s P)). Qed.
Lemma lem3600286 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P) = (term34 A s P)) = (term127 A _39018 s P).
Proof. exact (EQ_MP (@lem3600285 A _39018 s P) (@lem3600272 A _39018 s P)). Qed.
Lemma lem3600287 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)) = ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)).
Proof. exact (eq_refl ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P))). Qed.
Lemma lem3600288 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term126 A _39018 s P) = (term126 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3600287 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3600289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3600290 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term127 A _39018 s P) = (term127 A _39018 s P).
Proof. exact (MK_COMB (@lem3600289 A) (@lem3600288 A _39018 s P)). Qed.
Lemma lem3600291 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P) = (term34 A s P)) = (term127 A _39018 s P).
Proof. exact (TRANS (@lem3600286 A _39018 s P) (@lem3600290 A _39018 s P)). Qed.
Lemma lem3600292 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term115 A _39018 s) = (term128 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600291 A _39018 s P)). Qed.
Lemma lem3600293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600294 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term116 A _39018 s) = (term129 A _39018 s).
Proof. exact (MK_COMB (@lem3600293 A) (@lem3600292 A _39018 s)). Qed.
Lemma lem3600295 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((_39018 s) = (term31 A s)) = (term129 A _39018 s).
Proof. exact (TRANS (@lem3600268 A _39018 s) (@lem3600294 A _39018 s)). Qed.
Lemma lem3600296 {A : Type'} (_39018 : type636 A) : (term106 A _39018) = (term130 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600295 A _39018 s)). Qed.
Lemma lem3600297 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600298 {A : Type'} (_39018 : type636 A) : (term107 A _39018) = (term131 A _39018).
Proof. exact (MK_COMB (@lem3600297 A) (@lem3600296 A _39018)). Qed.
Lemma lem3600299 {A : Type'} (_39018 : type636 A) : (_39018 = (term29 A)) = (term131 A _39018).
Proof. exact (TRANS (@lem3600250 A _39018) (@lem3600298 A _39018)). Qed.
Lemma lem3600300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600301 {A : Type'} (_39018 : type636 A) : (term83 A _39018) = (term132 A _39018).
Proof. exact (MK_COMB (@lem3600300) (@lem3600299 A _39018)). Qed.
Lemma lem3600302 {_84465 A : Type'} (_39018 : type636 A) : (term74 _84465 A _39018) = (term74 _84465 A _39018).
Proof. exact (eq_refl (term74 _84465 A _39018)). Qed.
Lemma lem3600303 {_84465 A : Type'} (_39018 : type636 A) : (term91 _84465 A _39018) = (term133 _84465 A _39018).
Proof. exact (MK_COMB (@lem3600301 A _39018) (@lem3600302 _84465 A _39018)). Qed.
Lemma lem3600304 {_84465 A : Type'} : (term93 _84465 A) = (term134 _84465 A).
Proof. exact (fun_ext (fun _39018 : type636 A => @lem3600303 _84465 A _39018)). Qed.
Lemma lem3600305 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3600306 {_84465 A : Type'} : (term95 _84465 A) = (term135 _84465 A).
Proof. exact (MK_COMB (@lem3600305 A) (@lem3600304 _84465 A)). Qed.
Lemma lem3600307 {_84465 A : Type'} : (term82 _84465 A) = (term82 _84465 A).
Proof. exact (eq_refl (term82 _84465 A)). Qed.
Lemma lem3600308 {_84465 A : Type'} : ((term28 _84465 A) = (term95 _84465 A)) = ((term28 _84465 A) = (term135 _84465 A)).
Proof. exact (MK_COMB (@lem3600307 _84465 A) (@lem3600306 _84465 A)). Qed.
Lemma lem3600309 {_84465 A : Type'} : (term28 _84465 A) = (term135 _84465 A).
Proof. exact (EQ_MP (@lem3600308 _84465 A) (@lem3600232 _84465 A)). Qed.
Lemma lem3600310 {_84465 : Type'} (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : _39019 = (term29 _84465).
Proof. exact (h1). Qed.
Lemma lem3600311 {_84465 : Type'} (s : _84465 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3600312 {_84465 : Type'} (s : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (_39019 s) = (term30 _84465 s).
Proof. exact (MK_COMB (@lem3600310 _84465 _39019 h1) (@lem3600311 _84465 s)). Qed.
Lemma lem3600313 {_84465 : Type'} (s : _84465 -> Prop) : (term30 _84465 s) = (term31 _84465 s).
Proof. exact (eq_refl (term30 _84465 s)). Qed.
Lemma lem3600314 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term32 _84465 _39019 s) = (term32 _84465 _39019 s).
Proof. exact (eq_refl (term32 _84465 _39019 s)). Qed.
Lemma lem3600315 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((_39019 s) = (term30 _84465 s)) = ((_39019 s) = (term31 _84465 s)).
Proof. exact (MK_COMB (@lem3600314 _84465 _39019 s) (@lem3600313 _84465 s)). Qed.
Lemma lem3600316 {_84465 : Type'} (s : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (_39019 s) = (term31 _84465 s).
Proof. exact (EQ_MP (@lem3600315 _84465 _39019 s) (@lem3600312 _84465 s _39019 h1)). Qed.
Lemma lem3600317 {_84465 : Type'} (P : _84465 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3600318 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (_39019 s P) = (term33 _84465 s P).
Proof. exact (MK_COMB (@lem3600316 _84465 s _39019 h1) (@lem3600317 _84465 P)). Qed.
Lemma lem3600319 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term33 _84465 s P) = (term34 _84465 s P).
Proof. exact (eq_refl (term33 _84465 s P)). Qed.
Lemma lem3600320 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term35 _84465 _39019 s P) = (term35 _84465 _39019 s P).
Proof. exact (eq_refl (term35 _84465 _39019 s P)). Qed.
Lemma lem3600321 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P) = (term33 _84465 s P)) = ((_39019 s P) = (term34 _84465 s P)).
Proof. exact (MK_COMB (@lem3600320 _84465 _39019 s P) (@lem3600319 _84465 s P)). Qed.
Lemma lem3600322 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (_39019 s P) = (term34 _84465 s P).
Proof. exact (EQ_MP (@lem3600321 _84465 _39019 s P) (@lem3600318 _84465 s P _39019 h1)). Qed.
Lemma lem3600334 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term41 A _39018 P s) = (term41 A _39018 P s).
Proof. exact (eq_refl (term41 A _39018 P s)). Qed.
Lemma lem3600335 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term43 A _39018 s) = (term43 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600334 A _39018 P s)). Qed.
Lemma lem3600336 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600337 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term45 A _39018 s) = (term45 A _39018 s).
Proof. exact (MK_COMB (@lem3600336 A) (@lem3600335 A _39018 s)). Qed.
Lemma lem3600338 {A : Type'} (_39018 : type636 A) : (term47 A _39018) = (term47 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600337 A _39018 s)). Qed.
Lemma lem3600339 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600340 {A : Type'} (_39018 : type636 A) : (term48 A _39018) = (term48 A _39018).
Proof. exact (MK_COMB (@lem3600339 A) (@lem3600338 A _39018)). Qed.
Lemma lem3600341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600342 {A : Type'} (_39018 : type636 A) : (term49 A _39018) = (term49 A _39018).
Proof. exact (MK_COMB (@lem3600341) (@lem3600340 A _39018)). Qed.
Lemma lem3600343 {_84465 : Type'} (s : _84465 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3600345 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term34 _84465 s P) = (_39019 s P).
Proof. exact (SYM (@lem3600322 _84465 s P _39019 h1)). Qed.
Lemma lem3600346 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term34 _84465 s P) = (_39019 s P).
Proof. exact (@lem3600345 _84465 s P _39019 h1). Qed.
Lemma lem3600347 {_84465 : Type'} : (@GSPEC _84465) = (@GSPEC _84465).
Proof. exact (eq_refl (@GSPEC _84465)). Qed.
Lemma lem3600348 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term36 _84465 s P) = (term37 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600347 _84465) (@lem3600346 _84465 s P _39019 h1)). Qed.
Lemma lem3600349 {_84465 : Type'} : (@SUBSET _84465) = (@SUBSET _84465).
Proof. exact (eq_refl (@SUBSET _84465)). Qed.
Lemma lem3600350 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term38 _84465 s P) = (term39 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600349 _84465) (@lem3600348 _84465 s P _39019 h1)). Qed.
Lemma lem3600351 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term40 _84465 P s) = (term41 _84465 _39019 P s).
Proof. exact (MK_COMB (@lem3600350 _84465 s P _39019 h1) (@lem3600343 _84465 s)). Qed.
Lemma lem3600352 {_84465 : Type'} (s : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term42 _84465 s) = (term43 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600351 _84465 P s _39019 h1)). Qed.
Lemma lem3600353 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600354 {_84465 : Type'} (s : _84465 -> Prop) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term44 _84465 s) = (term45 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600353 _84465) (@lem3600352 _84465 s _39019 h1)). Qed.
Lemma lem3600355 {_84465 : Type'} (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term46 _84465) = (term47 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600354 _84465 s _39019 h1)). Qed.
Lemma lem3600356 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600357 {_84465 : Type'} (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term11 _84465) = (term48 _84465 _39019).
Proof. exact (MK_COMB (@lem3600356 _84465) (@lem3600355 _84465 _39019 h1)). Qed.
Lemma lem3600358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600359 {_84465 : Type'} (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term19 _84465) = (term136 _84465 _39019).
Proof. exact (MK_COMB (@lem3600358) (@lem3600357 _84465 _39019 h1)). Qed.
Lemma lem3600360 {_84465 A : Type'} (_39018 : type636 A) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term53 _84465 A _39018) = (term137 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600359 _84465 _39019 h1) (@lem3600342 A _39018)). Qed.
Lemma lem3600377 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term54 A t s).
Proof. exact (eq_refl (term54 A t s)). Qed.
Lemma lem3600378 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3600377 A t s)). Qed.
Lemma lem3600379 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600380 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3600379 A) (@lem3600378 A s)). Qed.
Lemma lem3600381 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600380 A s)). Qed.
Lemma lem3600382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600383 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3600382 A) (@lem3600381 A)). Qed.
Lemma lem3600384 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600385 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3600384) (@lem3600383 A)). Qed.
Lemma lem3600386 {_84465 A : Type'} (_39018 : type636 A) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term58 _84465 A _39018) = (term138 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600385 A) (@lem3600360 _84465 A _39018 _39019 h1)). Qed.
Lemma lem3600403 {_84465 : Type'} (t : _84465 -> Prop) (s : _84465 -> Prop) : (term54 _84465 t s) = (term54 _84465 t s).
Proof. exact (eq_refl (term54 _84465 t s)). Qed.
Lemma lem3600404 {_84465 : Type'} (s : _84465 -> Prop) : (term55 _84465 s) = (term55 _84465 s).
Proof. exact (fun_ext (fun t : _84465 -> Prop => @lem3600403 _84465 t s)). Qed.
Lemma lem3600405 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600406 {_84465 : Type'} (s : _84465 -> Prop) : (term56 _84465 s) = (term56 _84465 s).
Proof. exact (MK_COMB (@lem3600405 _84465) (@lem3600404 _84465 s)). Qed.
Lemma lem3600407 {_84465 : Type'} : (term57 _84465) = (term57 _84465).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600406 _84465 s)). Qed.
Lemma lem3600408 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600409 {_84465 : Type'} : (term12 _84465) = (term12 _84465).
Proof. exact (MK_COMB (@lem3600408 _84465) (@lem3600407 _84465)). Qed.
Lemma lem3600410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600411 {_84465 : Type'} : (term22 _84465) = (term22 _84465).
Proof. exact (MK_COMB (@lem3600410) (@lem3600409 _84465)). Qed.
Lemma lem3600412 {_84465 A : Type'} (_39018 : type636 A) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term59 _84465 A _39018) = (term139 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600411 _84465) (@lem3600386 _84465 A _39018 _39019 h1)). Qed.
Lemma lem3600427 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term64 A _39018 s P) = (term64 A _39018 s P).
Proof. exact (eq_refl (term64 A _39018 s P)). Qed.
Lemma lem3600428 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term66 A _39018 s) = (term66 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600427 A _39018 s P)). Qed.
Lemma lem3600429 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600430 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term68 A _39018 s) = (term68 A _39018 s).
Proof. exact (MK_COMB (@lem3600429 A) (@lem3600428 A _39018 s)). Qed.
Lemma lem3600431 {A : Type'} (_39018 : type636 A) : (term70 A _39018) = (term70 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600430 A _39018 s)). Qed.
Lemma lem3600432 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600433 {A : Type'} (_39018 : type636 A) : (term71 A _39018) = (term71 A _39018).
Proof. exact (MK_COMB (@lem3600432 A) (@lem3600431 A _39018)). Qed.
Lemma lem3600434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600435 {A : Type'} (_39018 : type636 A) : (term72 A _39018) = (term72 A _39018).
Proof. exact (MK_COMB (@lem3600434) (@lem3600433 A _39018)). Qed.
Lemma lem3600436 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600437 {A : Type'} (_39018 : type636 A) : (term73 A _39018) = (term73 A _39018).
Proof. exact (MK_COMB (@lem3600436) (@lem3600435 A _39018)). Qed.
Lemma lem3600438 {_84465 A : Type'} (_39018 : type636 A) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term74 _84465 A _39018) = (term140 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600437 A _39018) (@lem3600412 _84465 A _39018 _39019 h1)). Qed.
Lemma lem3600455 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term50 A GEN_PVAR_91 s P x) = (term50 A GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term50 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3600456 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term51 A GEN_PVAR_91 s P) = (term51 A GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3600455 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3600457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3600458 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term52 A GEN_PVAR_91 s P) = (term52 A GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3600457 A) (@lem3600456 A GEN_PVAR_91 s P)). Qed.
Lemma lem3600467 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term124 A _39018 s P GEN_PVAR_91) = (term124 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term124 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3600468 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)) = ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)).
Proof. exact (MK_COMB (@lem3600467 A _39018 s P GEN_PVAR_91) (@lem3600458 A GEN_PVAR_91 s P)). Qed.
Lemma lem3600469 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term126 A _39018 s P) = (term126 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3600468 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3600470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3600471 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term127 A _39018 s P) = (term127 A _39018 s P).
Proof. exact (MK_COMB (@lem3600470 A) (@lem3600469 A _39018 s P)). Qed.
Lemma lem3600472 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term128 A _39018 s) = (term128 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600471 A _39018 s P)). Qed.
Lemma lem3600473 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600474 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term129 A _39018 s) = (term129 A _39018 s).
Proof. exact (MK_COMB (@lem3600473 A) (@lem3600472 A _39018 s)). Qed.
Lemma lem3600475 {A : Type'} (_39018 : type636 A) : (term130 A _39018) = (term130 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600474 A _39018 s)). Qed.
Lemma lem3600476 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600477 {A : Type'} (_39018 : type636 A) : (term131 A _39018) = (term131 A _39018).
Proof. exact (MK_COMB (@lem3600476 A) (@lem3600475 A _39018)). Qed.
Lemma lem3600478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600479 {A : Type'} (_39018 : type636 A) : (term132 A _39018) = (term132 A _39018).
Proof. exact (MK_COMB (@lem3600478) (@lem3600477 A _39018)). Qed.
Lemma lem3600480 {_84465 A : Type'} (_39018 : type636 A) (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term133 _84465 A _39018) = (term141 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600479 A _39018) (@lem3600438 _84465 A _39018 _39019 h1)). Qed.
Lemma lem3600481 {_84465 A : Type'} (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term134 _84465 A) = (term142 _84465 A _39019).
Proof. exact (fun_ext (fun _39018 : type636 A => @lem3600480 _84465 A _39018 _39019 h1)). Qed.
Lemma lem3600482 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3600483 {_84465 A : Type'} (_39019 : type636 _84465) (h1 : _39019 = (term29 _84465)) : (term135 _84465 A) = (term143 _84465 A _39019).
Proof. exact (MK_COMB (@lem3600482 A) (@lem3600481 _84465 A _39019 h1)). Qed.
Lemma lem3600484 {_84465 A : Type'} (_39019 : type636 _84465) : term144 _84465 A _39019.
Proof. exact (fun h0 : _39019 = (term29 _84465) => @lem3600483 _84465 A _39019 h0). Qed.
Lemma lem3600485 {_84465 A : Type'} : term145 _84465 A.
Proof. exact (fun _39019 : type636 _84465 => @lem3600484 _84465 A _39019). Qed.
Lemma lem3600487 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term77 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem3600488 {_84465 : Type'} (P : Prop) (c : type636 _84465) (Q : type138 _84465) : term78 _84465 P c Q.
Proof. exact (@lem3600487 (type636 _84465) P c Q). Qed.
Lemma lem3600489 {_84465 A : Type'} : term146 _84465 A.
Proof. exact (@lem3600488 _84465 (term135 _84465 A) (term29 _84465) (term147 _84465 A)). Qed.
Lemma lem3600490 {_84465 A : Type'} (_39019 : type636 _84465) : (term148 _84465 A _39019) = (term143 _84465 A _39019).
Proof. exact (eq_refl (term148 _84465 A _39019)). Qed.
Lemma lem3600491 {_84465 A : Type'} : (term149 _84465 A) = (term149 _84465 A).
Proof. exact (eq_refl (term149 _84465 A)). Qed.
Lemma lem3600492 {_84465 A : Type'} (_39019 : type636 _84465) : ((term135 _84465 A) = (term148 _84465 A _39019)) = ((term135 _84465 A) = (term143 _84465 A _39019)).
Proof. exact (MK_COMB (@lem3600491 _84465 A) (@lem3600490 _84465 A _39019)). Qed.
Lemma lem3600493 {_84465 : Type'} (_39019 : type636 _84465) : (term83 _84465 _39019) = (term83 _84465 _39019).
Proof. exact (eq_refl (term83 _84465 _39019)). Qed.
Lemma lem3600494 {_84465 A : Type'} (_39019 : type636 _84465) : (term150 _84465 A _39019) = (term144 _84465 A _39019).
Proof. exact (MK_COMB (@lem3600493 _84465 _39019) (@lem3600492 _84465 A _39019)). Qed.
Lemma lem3600495 {_84465 A : Type'} : (term151 _84465 A) = (term152 _84465 A).
Proof. exact (fun_ext (fun _39019 : type636 _84465 => @lem3600494 _84465 A _39019)). Qed.
Lemma lem3600496 {_84465 : Type'} : (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)) = (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)).
Proof. exact (eq_refl (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop))). Qed.
Lemma lem3600497 {_84465 A : Type'} : (term153 _84465 A) = (term145 _84465 A).
Proof. exact (MK_COMB (@lem3600496 _84465) (@lem3600495 _84465 A)). Qed.
Lemma lem3600498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600499 {_84465 A : Type'} : (term154 _84465 A) = (term155 _84465 A).
Proof. exact (MK_COMB (@lem3600498) (@lem3600497 _84465 A)). Qed.
Lemma lem3600500 {_84465 A : Type'} (_39019 : type636 _84465) : (term148 _84465 A _39019) = (term143 _84465 A _39019).
Proof. exact (eq_refl (term148 _84465 A _39019)). Qed.
Lemma lem3600501 {_84465 : Type'} (_39019 : type636 _84465) : (term83 _84465 _39019) = (term83 _84465 _39019).
Proof. exact (eq_refl (term83 _84465 _39019)). Qed.
Lemma lem3600502 {_84465 A : Type'} (_39019 : type636 _84465) : (term156 _84465 A _39019) = (term157 _84465 A _39019).
Proof. exact (MK_COMB (@lem3600501 _84465 _39019) (@lem3600500 _84465 A _39019)). Qed.
Lemma lem3600503 {_84465 A : Type'} : (term158 _84465 A) = (term159 _84465 A).
Proof. exact (fun_ext (fun _39019 : type636 _84465 => @lem3600502 _84465 A _39019)). Qed.
Lemma lem3600504 {_84465 : Type'} : (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)) = (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)).
Proof. exact (eq_refl (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop))). Qed.
Lemma lem3600505 {_84465 A : Type'} : (term160 _84465 A) = (term161 _84465 A).
Proof. exact (MK_COMB (@lem3600504 _84465) (@lem3600503 _84465 A)). Qed.
Lemma lem3600506 {_84465 A : Type'} : (term149 _84465 A) = (term149 _84465 A).
Proof. exact (eq_refl (term149 _84465 A)). Qed.
Lemma lem3600507 {_84465 A : Type'} : ((term135 _84465 A) = (term160 _84465 A)) = ((term135 _84465 A) = (term161 _84465 A)).
Proof. exact (MK_COMB (@lem3600506 _84465 A) (@lem3600505 _84465 A)). Qed.
Lemma lem3600508 {_84465 A : Type'} : (term146 _84465 A) = (term162 _84465 A).
Proof. exact (MK_COMB (@lem3600499 _84465 A) (@lem3600507 _84465 A)). Qed.
Lemma lem3600509 {_84465 A : Type'} : term162 _84465 A.
Proof. exact (EQ_MP (@lem3600508 _84465 A) (@lem3600489 _84465 A)). Qed.
Lemma lem3600510 {_84465 A : Type'} : (term135 _84465 A) = (term161 _84465 A).
Proof. exact (@lem3600509 _84465 A (@lem3600485 _84465 A)). Qed.
Lemma lem3600512 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term97 _3571 _3575 t)) = (term98 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem3600513 {_84465 : Type'} (s : type636 _84465) (t : type636 _84465) : (s = (term99 _84465 t)) = (term100 _84465 s t).
Proof. exact (@lem3600512 (type672 _84465) (_84465 -> Prop) s t). Qed.
Lemma lem3600514 {_84465 : Type'} (_39019 : type636 _84465) : (_39019 = (term101 _84465)) = (term102 _84465 _39019).
Proof. exact (@lem3600513 _84465 _39019 (term29 _84465)). Qed.
Lemma lem3600515 {_84465 : Type'} (s : _84465 -> Prop) : (term30 _84465 s) = (term31 _84465 s).
Proof. exact (eq_refl (term30 _84465 s)). Qed.
Lemma lem3600516 {_84465 : Type'} : (term101 _84465) = (term29 _84465).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600515 _84465 s)). Qed.
Lemma lem3600517 {_84465 : Type'} (_39019 : type636 _84465) : (@eq ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop) _39019) = (@eq ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop) _39019).
Proof. exact (eq_refl (@eq ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop) _39019)). Qed.
Lemma lem3600518 {_84465 : Type'} (_39019 : type636 _84465) : (_39019 = (term101 _84465)) = (_39019 = (term29 _84465)).
Proof. exact (MK_COMB (@lem3600517 _84465 _39019) (@lem3600516 _84465)). Qed.
Lemma lem3600519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600520 {_84465 : Type'} (_39019 : type636 _84465) : (term103 _84465 _39019) = (term104 _84465 _39019).
Proof. exact (MK_COMB (@lem3600519) (@lem3600518 _84465 _39019)). Qed.
Lemma lem3600521 {_84465 : Type'} (s : _84465 -> Prop) : (term30 _84465 s) = (term31 _84465 s).
Proof. exact (eq_refl (term30 _84465 s)). Qed.
Lemma lem3600522 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term32 _84465 _39019 s) = (term32 _84465 _39019 s).
Proof. exact (eq_refl (term32 _84465 _39019 s)). Qed.
Lemma lem3600523 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((_39019 s) = (term30 _84465 s)) = ((_39019 s) = (term31 _84465 s)).
Proof. exact (MK_COMB (@lem3600522 _84465 _39019 s) (@lem3600521 _84465 s)). Qed.
Lemma lem3600524 {_84465 : Type'} (_39019 : type636 _84465) : (term105 _84465 _39019) = (term106 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600523 _84465 _39019 s)). Qed.
Lemma lem3600525 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600526 {_84465 : Type'} (_39019 : type636 _84465) : (term102 _84465 _39019) = (term107 _84465 _39019).
Proof. exact (MK_COMB (@lem3600525 _84465) (@lem3600524 _84465 _39019)). Qed.
Lemma lem3600527 {_84465 : Type'} (_39019 : type636 _84465) : ((_39019 = (term101 _84465)) = (term102 _84465 _39019)) = ((_39019 = (term29 _84465)) = (term107 _84465 _39019)).
Proof. exact (MK_COMB (@lem3600520 _84465 _39019) (@lem3600526 _84465 _39019)). Qed.
Lemma lem3600528 {_84465 : Type'} (_39019 : type636 _84465) : (_39019 = (term29 _84465)) = (term107 _84465 _39019).
Proof. exact (EQ_MP (@lem3600527 _84465 _39019) (@lem3600514 _84465 _39019)). Qed.
Lemma lem3600530 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term97 _3571 _3575 t)) = (term98 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem3600531 {_84465 : Type'} (s : type672 _84465) (t : type672 _84465) : (s = (term108 _84465 t)) = (term109 _84465 s t).
Proof. exact (@lem3600530 (_84465 -> Prop) (_84465 -> Prop) s t). Qed.
Lemma lem3600532 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((_39019 s) = (term110 _84465 s)) = (term111 _84465 _39019 s).
Proof. exact (@lem3600531 _84465 (_39019 s) (term31 _84465 s)). Qed.
Lemma lem3600533 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term33 _84465 s P) = (term34 _84465 s P).
Proof. exact (eq_refl (term33 _84465 s P)). Qed.
Lemma lem3600534 {_84465 : Type'} (s : _84465 -> Prop) : (term110 _84465 s) = (term31 _84465 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600533 _84465 s P)). Qed.
Lemma lem3600535 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term32 _84465 _39019 s) = (term32 _84465 _39019 s).
Proof. exact (eq_refl (term32 _84465 _39019 s)). Qed.
Lemma lem3600536 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((_39019 s) = (term110 _84465 s)) = ((_39019 s) = (term31 _84465 s)).
Proof. exact (MK_COMB (@lem3600535 _84465 _39019 s) (@lem3600534 _84465 s)). Qed.
Lemma lem3600537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600538 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term112 _84465 _39019 s) = (term113 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600537) (@lem3600536 _84465 _39019 s)). Qed.
Lemma lem3600539 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term33 _84465 s P) = (term34 _84465 s P).
Proof. exact (eq_refl (term33 _84465 s P)). Qed.
Lemma lem3600540 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term35 _84465 _39019 s P) = (term35 _84465 _39019 s P).
Proof. exact (eq_refl (term35 _84465 _39019 s P)). Qed.
Lemma lem3600541 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P) = (term33 _84465 s P)) = ((_39019 s P) = (term34 _84465 s P)).
Proof. exact (MK_COMB (@lem3600540 _84465 _39019 s P) (@lem3600539 _84465 s P)). Qed.
Lemma lem3600542 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term114 _84465 _39019 s) = (term115 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600541 _84465 _39019 s P)). Qed.
Lemma lem3600543 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600544 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term111 _84465 _39019 s) = (term116 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600543 _84465) (@lem3600542 _84465 _39019 s)). Qed.
Lemma lem3600545 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (((_39019 s) = (term110 _84465 s)) = (term111 _84465 _39019 s)) = (((_39019 s) = (term31 _84465 s)) = (term116 _84465 _39019 s)).
Proof. exact (MK_COMB (@lem3600538 _84465 _39019 s) (@lem3600544 _84465 _39019 s)). Qed.
Lemma lem3600546 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((_39019 s) = (term31 _84465 s)) = (term116 _84465 _39019 s).
Proof. exact (EQ_MP (@lem3600545 _84465 _39019 s) (@lem3600532 _84465 _39019 s)). Qed.
Lemma lem3600548 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term97 _3571 _3575 t)) = (term98 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem3600549 {_84465 : Type'} (s : _84465 -> Prop) (t : _84465 -> Prop) : (s = (term117 _84465 t)) = (term118 _84465 s t).
Proof. exact (@lem3600548 Prop _84465 s t). Qed.
Lemma lem3600550 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P) = (term119 _84465 s P)) = (term120 _84465 _39019 s P).
Proof. exact (@lem3600549 _84465 (_39019 s P) (term34 _84465 s P)). Qed.
Lemma lem3600551 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term121 _84465 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term121 _84465 s P GEN_PVAR_11)). Qed.
Lemma lem3600552 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : (term119 _84465 s P) = (term34 _84465 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600551 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600553 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term35 _84465 _39019 s P) = (term35 _84465 _39019 s P).
Proof. exact (eq_refl (term35 _84465 _39019 s P)). Qed.
Lemma lem3600554 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P) = (term119 _84465 s P)) = ((_39019 s P) = (term34 _84465 s P)).
Proof. exact (MK_COMB (@lem3600553 _84465 _39019 s P) (@lem3600552 _84465 s P)). Qed.
Lemma lem3600555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600556 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term122 _84465 _39019 s P) = (term123 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600555) (@lem3600554 _84465 _39019 s P)). Qed.
Lemma lem3600557 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term121 _84465 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term121 _84465 s P GEN_PVAR_11)). Qed.
Lemma lem3600558 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (GEN_PVAR_11 : _84465) : (term124 _84465 _39019 s P GEN_PVAR_11) = (term124 _84465 _39019 s P GEN_PVAR_11).
Proof. exact (eq_refl (term124 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600559 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P GEN_PVAR_11) = (term121 _84465 s P GEN_PVAR_11)) = ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)).
Proof. exact (MK_COMB (@lem3600558 _84465 _39019 s P GEN_PVAR_11) (@lem3600557 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600560 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term125 _84465 _39019 s P) = (term126 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600559 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600561 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600562 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term120 _84465 _39019 s P) = (term127 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600561 _84465) (@lem3600560 _84465 _39019 s P)). Qed.
Lemma lem3600563 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (((_39019 s P) = (term119 _84465 s P)) = (term120 _84465 _39019 s P)) = (((_39019 s P) = (term34 _84465 s P)) = (term127 _84465 _39019 s P)).
Proof. exact (MK_COMB (@lem3600556 _84465 _39019 s P) (@lem3600562 _84465 _39019 s P)). Qed.
Lemma lem3600564 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P) = (term34 _84465 s P)) = (term127 _84465 _39019 s P).
Proof. exact (EQ_MP (@lem3600563 _84465 _39019 s P) (@lem3600550 _84465 _39019 s P)). Qed.
Lemma lem3600565 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)) = ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)).
Proof. exact (eq_refl ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P))). Qed.
Lemma lem3600566 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term126 _84465 _39019 s P) = (term126 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600565 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600567 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600568 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term127 _84465 _39019 s P) = (term127 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600567 _84465) (@lem3600566 _84465 _39019 s P)). Qed.
Lemma lem3600569 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P) = (term34 _84465 s P)) = (term127 _84465 _39019 s P).
Proof. exact (TRANS (@lem3600564 _84465 _39019 s P) (@lem3600568 _84465 _39019 s P)). Qed.
Lemma lem3600570 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term115 _84465 _39019 s) = (term128 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600569 _84465 _39019 s P)). Qed.
Lemma lem3600571 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600572 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term116 _84465 _39019 s) = (term129 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600571 _84465) (@lem3600570 _84465 _39019 s)). Qed.
Lemma lem3600573 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((_39019 s) = (term31 _84465 s)) = (term129 _84465 _39019 s).
Proof. exact (TRANS (@lem3600546 _84465 _39019 s) (@lem3600572 _84465 _39019 s)). Qed.
Lemma lem3600574 {_84465 : Type'} (_39019 : type636 _84465) : (term106 _84465 _39019) = (term130 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600573 _84465 _39019 s)). Qed.
Lemma lem3600575 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600576 {_84465 : Type'} (_39019 : type636 _84465) : (term107 _84465 _39019) = (term131 _84465 _39019).
Proof. exact (MK_COMB (@lem3600575 _84465) (@lem3600574 _84465 _39019)). Qed.
Lemma lem3600577 {_84465 : Type'} (_39019 : type636 _84465) : (_39019 = (term29 _84465)) = (term131 _84465 _39019).
Proof. exact (TRANS (@lem3600528 _84465 _39019) (@lem3600576 _84465 _39019)). Qed.
Lemma lem3600578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600579 {_84465 : Type'} (_39019 : type636 _84465) : (term83 _84465 _39019) = (term132 _84465 _39019).
Proof. exact (MK_COMB (@lem3600578) (@lem3600577 _84465 _39019)). Qed.
Lemma lem3600580 {_84465 A : Type'} (_39019 : type636 _84465) : (term143 _84465 A _39019) = (term143 _84465 A _39019).
Proof. exact (eq_refl (term143 _84465 A _39019)). Qed.
Lemma lem3600581 {_84465 A : Type'} (_39019 : type636 _84465) : (term157 _84465 A _39019) = (term163 _84465 A _39019).
Proof. exact (MK_COMB (@lem3600579 _84465 _39019) (@lem3600580 _84465 A _39019)). Qed.
Lemma lem3600582 {_84465 A : Type'} : (term159 _84465 A) = (term164 _84465 A).
Proof. exact (fun_ext (fun _39019 : type636 _84465 => @lem3600581 _84465 A _39019)). Qed.
Lemma lem3600583 {_84465 : Type'} : (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)) = (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)).
Proof. exact (eq_refl (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop))). Qed.
Lemma lem3600584 {_84465 A : Type'} : (term161 _84465 A) = (term165 _84465 A).
Proof. exact (MK_COMB (@lem3600583 _84465) (@lem3600582 _84465 A)). Qed.
Lemma lem3600585 {_84465 A : Type'} : (term149 _84465 A) = (term149 _84465 A).
Proof. exact (eq_refl (term149 _84465 A)). Qed.
Lemma lem3600586 {_84465 A : Type'} : ((term135 _84465 A) = (term161 _84465 A)) = ((term135 _84465 A) = (term165 _84465 A)).
Proof. exact (MK_COMB (@lem3600585 _84465 A) (@lem3600584 _84465 A)). Qed.
Lemma lem3600589 {_84465 A : Type'} : (term135 _84465 A) = (term165 _84465 A).
Proof. exact (EQ_MP (@lem3600586 _84465 A) (@lem3600510 _84465 A)). Qed.
Lemma lem3600590 {_84465 A : Type'} : (term28 _84465 A) = (term165 _84465 A).
Proof. exact (TRANS (@lem3600309 _84465 A) (@lem3600589 _84465 A)). Qed.
Lemma lem3600591 {_84465 A : Type'} : (term13 _84465 A) = (term165 _84465 A).
Proof. exact (TRANS (@lem3600059 _84465 A) (@lem3600590 _84465 A)). Qed.
Lemma lem3600592 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term41 A _39018 P s) = (term41 A _39018 P s).
Proof. exact (eq_refl (term41 A _39018 P s)). Qed.
Lemma lem3600593 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term43 A _39018 s) = (term43 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600592 A _39018 P s)). Qed.
Lemma lem3600594 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600595 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term45 A _39018 s) = (term45 A _39018 s).
Proof. exact (MK_COMB (@lem3600594 A) (@lem3600593 A _39018 s)). Qed.
Lemma lem3600596 {A : Type'} (_39018 : type636 A) : (term47 A _39018) = (term47 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600595 A _39018 s)). Qed.
Lemma lem3600597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600598 {A : Type'} (_39018 : type636 A) : (term48 A _39018) = (term48 A _39018).
Proof. exact (MK_COMB (@lem3600597 A) (@lem3600596 A _39018)). Qed.
Lemma lem3600599 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600600 {A : Type'} (_39018 : type636 A) : (term49 A _39018) = (term49 A _39018).
Proof. exact (MK_COMB (@lem3600599) (@lem3600598 A _39018)). Qed.
Lemma lem3600601 {_84465 : Type'} (_39019 : type636 _84465) (P : _84465 -> Prop) (s : _84465 -> Prop) : (term41 _84465 _39019 P s) = (term41 _84465 _39019 P s).
Proof. exact (eq_refl (term41 _84465 _39019 P s)). Qed.
Lemma lem3600602 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term43 _84465 _39019 s) = (term43 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600601 _84465 _39019 P s)). Qed.
Lemma lem3600603 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600604 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term45 _84465 _39019 s) = (term45 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600603 _84465) (@lem3600602 _84465 _39019 s)). Qed.
Lemma lem3600605 {_84465 : Type'} (_39019 : type636 _84465) : (term47 _84465 _39019) = (term47 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600604 _84465 _39019 s)). Qed.
Lemma lem3600606 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600607 {_84465 : Type'} (_39019 : type636 _84465) : (term48 _84465 _39019) = (term48 _84465 _39019).
Proof. exact (MK_COMB (@lem3600606 _84465) (@lem3600605 _84465 _39019)). Qed.
Lemma lem3600608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600609 {_84465 : Type'} (_39019 : type636 _84465) : (term136 _84465 _39019) = (term136 _84465 _39019).
Proof. exact (MK_COMB (@lem3600608) (@lem3600607 _84465 _39019)). Qed.
Lemma lem3600610 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) : (term137 _84465 A _39019 _39018) = (term137 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600609 _84465 _39019) (@lem3600600 A _39018)). Qed.
Lemma lem3600619 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term54 A t s).
Proof. exact (eq_refl (term54 A t s)). Qed.
Lemma lem3600620 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3600619 A t s)). Qed.
Lemma lem3600621 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600622 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3600621 A) (@lem3600620 A s)). Qed.
Lemma lem3600623 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600622 A s)). Qed.
Lemma lem3600624 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600625 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3600624 A) (@lem3600623 A)). Qed.
Lemma lem3600626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600627 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3600626) (@lem3600625 A)). Qed.
Lemma lem3600628 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) : (term138 _84465 A _39019 _39018) = (term138 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600627 A) (@lem3600610 _84465 A _39019 _39018)). Qed.
Lemma lem3600637 {_84465 : Type'} (t : _84465 -> Prop) (s : _84465 -> Prop) : (term54 _84465 t s) = (term54 _84465 t s).
Proof. exact (eq_refl (term54 _84465 t s)). Qed.
Lemma lem3600638 {_84465 : Type'} (s : _84465 -> Prop) : (term55 _84465 s) = (term55 _84465 s).
Proof. exact (fun_ext (fun t : _84465 -> Prop => @lem3600637 _84465 t s)). Qed.
Lemma lem3600639 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600640 {_84465 : Type'} (s : _84465 -> Prop) : (term56 _84465 s) = (term56 _84465 s).
Proof. exact (MK_COMB (@lem3600639 _84465) (@lem3600638 _84465 s)). Qed.
Lemma lem3600641 {_84465 : Type'} : (term57 _84465) = (term57 _84465).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600640 _84465 s)). Qed.
Lemma lem3600642 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600643 {_84465 : Type'} : (term12 _84465) = (term12 _84465).
Proof. exact (MK_COMB (@lem3600642 _84465) (@lem3600641 _84465)). Qed.
Lemma lem3600644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600645 {_84465 : Type'} : (term22 _84465) = (term22 _84465).
Proof. exact (MK_COMB (@lem3600644) (@lem3600643 _84465)). Qed.
Lemma lem3600646 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) : (term139 _84465 A _39019 _39018) = (term139 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600645 _84465) (@lem3600628 _84465 A _39019 _39018)). Qed.
Lemma lem3600651 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term64 A _39018 s P) = (term64 A _39018 s P).
Proof. exact (eq_refl (term64 A _39018 s P)). Qed.
Lemma lem3600652 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term66 A _39018 s) = (term66 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600651 A _39018 s P)). Qed.
Lemma lem3600653 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600654 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term68 A _39018 s) = (term68 A _39018 s).
Proof. exact (MK_COMB (@lem3600653 A) (@lem3600652 A _39018 s)). Qed.
Lemma lem3600655 {A : Type'} (_39018 : type636 A) : (term70 A _39018) = (term70 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600654 A _39018 s)). Qed.
Lemma lem3600656 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600657 {A : Type'} (_39018 : type636 A) : (term71 A _39018) = (term71 A _39018).
Proof. exact (MK_COMB (@lem3600656 A) (@lem3600655 A _39018)). Qed.
Lemma lem3600658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600659 {A : Type'} (_39018 : type636 A) : (term72 A _39018) = (term72 A _39018).
Proof. exact (MK_COMB (@lem3600658) (@lem3600657 A _39018)). Qed.
Lemma lem3600660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600661 {A : Type'} (_39018 : type636 A) : (term73 A _39018) = (term73 A _39018).
Proof. exact (MK_COMB (@lem3600660) (@lem3600659 A _39018)). Qed.
Lemma lem3600662 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) : (term140 _84465 A _39019 _39018) = (term140 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600661 A _39018) (@lem3600646 _84465 A _39019 _39018)). Qed.
Lemma lem3600663 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term50 A GEN_PVAR_91 s P x) = (term50 A GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term50 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3600664 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term51 A GEN_PVAR_91 s P) = (term51 A GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3600663 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3600665 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3600666 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term52 A GEN_PVAR_91 s P) = (term52 A GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3600665 A) (@lem3600664 A GEN_PVAR_91 s P)). Qed.
Lemma lem3600669 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term124 A _39018 s P GEN_PVAR_91) = (term124 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term124 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3600670 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)) = ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)).
Proof. exact (MK_COMB (@lem3600669 A _39018 s P GEN_PVAR_91) (@lem3600666 A GEN_PVAR_91 s P)). Qed.
Lemma lem3600671 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term126 A _39018 s P) = (term126 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3600670 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3600672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3600673 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term127 A _39018 s P) = (term127 A _39018 s P).
Proof. exact (MK_COMB (@lem3600672 A) (@lem3600671 A _39018 s P)). Qed.
Lemma lem3600674 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term128 A _39018 s) = (term128 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3600673 A _39018 s P)). Qed.
Lemma lem3600675 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600676 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term129 A _39018 s) = (term129 A _39018 s).
Proof. exact (MK_COMB (@lem3600675 A) (@lem3600674 A _39018 s)). Qed.
Lemma lem3600677 {A : Type'} (_39018 : type636 A) : (term130 A _39018) = (term130 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3600676 A _39018 s)). Qed.
Lemma lem3600678 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3600679 {A : Type'} (_39018 : type636 A) : (term131 A _39018) = (term131 A _39018).
Proof. exact (MK_COMB (@lem3600678 A) (@lem3600677 A _39018)). Qed.
Lemma lem3600680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600681 {A : Type'} (_39018 : type636 A) : (term132 A _39018) = (term132 A _39018).
Proof. exact (MK_COMB (@lem3600680) (@lem3600679 A _39018)). Qed.
Lemma lem3600682 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) : (term141 _84465 A _39019 _39018) = (term141 _84465 A _39019 _39018).
Proof. exact (MK_COMB (@lem3600681 A _39018) (@lem3600662 _84465 A _39019 _39018)). Qed.
Lemma lem3600683 {_84465 A : Type'} (_39019 : type636 _84465) : (term142 _84465 A _39019) = (term142 _84465 A _39019).
Proof. exact (fun_ext (fun _39018 : type636 A => @lem3600682 _84465 A _39019 _39018)). Qed.
Lemma lem3600684 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3600685 {_84465 A : Type'} (_39019 : type636 _84465) : (term143 _84465 A _39019) = (term143 _84465 A _39019).
Proof. exact (MK_COMB (@lem3600684 A) (@lem3600683 _84465 A _39019)). Qed.
Lemma lem3600686 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term50 _84465 GEN_PVAR_11 s P x) = (term50 _84465 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term50 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600687 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term51 _84465 GEN_PVAR_11 s P) = (term51 _84465 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3600686 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600688 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3600689 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term52 _84465 GEN_PVAR_11 s P) = (term52 _84465 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600688 _84465) (@lem3600687 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600692 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (GEN_PVAR_11 : _84465) : (term124 _84465 _39019 s P GEN_PVAR_11) = (term124 _84465 _39019 s P GEN_PVAR_11).
Proof. exact (eq_refl (term124 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600693 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)) = ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)).
Proof. exact (MK_COMB (@lem3600692 _84465 _39019 s P GEN_PVAR_11) (@lem3600689 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600694 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term126 _84465 _39019 s P) = (term126 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600693 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600695 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600696 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term127 _84465 _39019 s P) = (term127 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600695 _84465) (@lem3600694 _84465 _39019 s P)). Qed.
Lemma lem3600697 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term128 _84465 _39019 s) = (term128 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600696 _84465 _39019 s P)). Qed.
Lemma lem3600698 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600699 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term129 _84465 _39019 s) = (term129 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600698 _84465) (@lem3600697 _84465 _39019 s)). Qed.
Lemma lem3600700 {_84465 : Type'} (_39019 : type636 _84465) : (term130 _84465 _39019) = (term130 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600699 _84465 _39019 s)). Qed.
Lemma lem3600701 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600702 {_84465 : Type'} (_39019 : type636 _84465) : (term131 _84465 _39019) = (term131 _84465 _39019).
Proof. exact (MK_COMB (@lem3600701 _84465) (@lem3600700 _84465 _39019)). Qed.
Lemma lem3600703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3600704 {_84465 : Type'} (_39019 : type636 _84465) : (term132 _84465 _39019) = (term132 _84465 _39019).
Proof. exact (MK_COMB (@lem3600703) (@lem3600702 _84465 _39019)). Qed.
Lemma lem3600705 {_84465 A : Type'} (_39019 : type636 _84465) : (term163 _84465 A _39019) = (term163 _84465 A _39019).
Proof. exact (MK_COMB (@lem3600704 _84465 _39019) (@lem3600685 _84465 A _39019)). Qed.
Lemma lem3600706 {_84465 A : Type'} : (term164 _84465 A) = (term164 _84465 A).
Proof. exact (fun_ext (fun _39019 : type636 _84465 => @lem3600705 _84465 A _39019)). Qed.
Lemma lem3600707 {_84465 : Type'} : (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)) = (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop)).
Proof. exact (eq_refl (@all ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> Prop))). Qed.
Lemma lem3600708 {_84465 A : Type'} : (term165 _84465 A) = (term165 _84465 A).
Proof. exact (MK_COMB (@lem3600707 _84465) (@lem3600706 _84465 A)). Qed.
Lemma lem3600857 {_84465 A : Type'} : (term13 _84465 A) = (term165 _84465 A).
Proof. exact (TRANS (@lem3600591 _84465 A) (@lem3600708 _84465 A)). Qed.
Lemma lem3600858 {_84465 A : Type'} : (term165 _84465 A) = (term13 _84465 A).
Proof. exact (SYM (@lem3600857 _84465 A)). Qed.
Lemma lem3600859 {_84465 : Type'} (_39019 : type636 _84465) (h1 : term131 _84465 _39019) : term131 _84465 _39019.
Proof. exact (h1). Qed.
Lemma lem3600860 {A : Type'} (_39018 : type636 A) (h1 : term131 A _39018) : term131 A _39018.
Proof. exact (h1). Qed.
Lemma lem3600861 {A : Type'} (_39018 : type636 A) (h1 : term72 A _39018) : term72 A _39018.
Proof. exact (h1). Qed.
Lemma lem3600863 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3600865 {A : Type'} (_39018 : type636 A) (h1 : term48 A _39018) : term48 A _39018.
Proof. exact (h1). Qed.
Lemma lem3600869 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term50 _84465 GEN_PVAR_11 s P x) = (term50 _84465 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term50 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600870 {_84465 : Type'} (P : _84465 -> Prop) : (term166 _84465 P) = (term167 _84465 P).
Proof. exact (@lem18394 _84465 P). Qed.
Lemma lem3600871 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term168 _84465 GEN_PVAR_11 s P) = (term169 _84465 GEN_PVAR_11 s P).
Proof. exact (@lem3600870 _84465 (term51 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600872 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term170 _84465 GEN_PVAR_11 s P x) = (term50 _84465 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term170 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3600875 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term171 _84465 GEN_PVAR_11 s P x) = (term172 _84465 GEN_PVAR_11 s P x).
Proof. exact (MK_COMB (@lem3600873) (@lem3600872 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600876 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term173 _84465 GEN_PVAR_11 s P) = (term174 _84465 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3600875 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600877 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600878 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term169 _84465 GEN_PVAR_11 s P) = (term175 _84465 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600877 _84465) (@lem3600876 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600879 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term168 _84465 GEN_PVAR_11 s P) = (term175 _84465 GEN_PVAR_11 s P).
Proof. exact (TRANS (@lem3600871 _84465 GEN_PVAR_11 s P) (@lem3600878 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600880 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term51 _84465 GEN_PVAR_11 s P) = (term51 _84465 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3600869 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3600881 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3600882 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term52 _84465 GEN_PVAR_11 s P) = (term52 _84465 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600881 _84465) (@lem3600880 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600884 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (GEN_PVAR_11 : _84465) : (term176 _84465 _39019 s P GEN_PVAR_11) = (term176 _84465 _39019 s P GEN_PVAR_11).
Proof. exact (eq_refl (term176 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600885 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term177 _84465 _39019 GEN_PVAR_11 s P) = (term177 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600884 _84465 _39019 s P GEN_PVAR_11) (@lem3600882 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600887 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (GEN_PVAR_11 : _84465) : (term178 _84465 _39019 s P GEN_PVAR_11) = (term178 _84465 _39019 s P GEN_PVAR_11).
Proof. exact (eq_refl (term178 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600888 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term179 _84465 _39019 GEN_PVAR_11 s P) = (term180 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600887 _84465 _39019 s P GEN_PVAR_11) (@lem3600879 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3600890 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term181 _84465 _39019 GEN_PVAR_11 s P) = (term182 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600889) (@lem3600888 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600891 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term183 _84465 _39019 GEN_PVAR_11 s P) = (term184 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600890 _84465 _39019 GEN_PVAR_11 s P) (@lem3600885 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600892 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)) = (term183 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (@lem17784 (_39019 s P GEN_PVAR_11) (term52 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3600893 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((_39019 s P GEN_PVAR_11) = (term52 _84465 GEN_PVAR_11 s P)) = (term184 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (TRANS (@lem3600892 _84465 _39019 GEN_PVAR_11 s P) (@lem3600891 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600894 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term126 _84465 _39019 s P) = (term185 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600893 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600895 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600896 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term127 _84465 _39019 s P) = (term186 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600895 _84465) (@lem3600894 _84465 _39019 s P)). Qed.
Lemma lem3600897 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term128 _84465 _39019 s) = (term187 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600896 _84465 _39019 s P)). Qed.
Lemma lem3600898 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600899 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term129 _84465 _39019 s) = (term188 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3600898 _84465) (@lem3600897 _84465 _39019 s)). Qed.
Lemma lem3600900 {_84465 : Type'} (_39019 : type636 _84465) : (term130 _84465 _39019) = (term189 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3600899 _84465 _39019 s)). Qed.
Lemma lem3600901 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3600902 {_84465 : Type'} (_39019 : type636 _84465) : (term131 _84465 _39019) = (term190 _84465 _39019).
Proof. exact (MK_COMB (@lem3600901 _84465) (@lem3600900 _84465 _39019)). Qed.
Lemma lem3600912 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3600913 {_84465 : Type'} (P : _84465 -> Prop) (Q : _84465 -> Prop) : (term191 _84465 P Q) = (term192 _84465 P Q).
Proof. exact (@lem3600912 _84465 P Q). Qed.
Lemma lem3600914 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term193 _84465 _39019 s P) = (term194 _84465 _39019 s P).
Proof. exact (@lem3600913 _84465 (term195 _84465 _39019 s P) (term196 _84465 _39019 s P)). Qed.
Lemma lem3600915 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term197 _84465 _39019 s P GEN_PVAR_11) = (term180 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term197 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3600917 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term198 _84465 _39019 s P GEN_PVAR_11) = (term182 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600916) (@lem3600915 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600918 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term199 _84465 _39019 s P GEN_PVAR_11) = (term177 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term199 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600919 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term200 _84465 _39019 s P GEN_PVAR_11) = (term184 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3600917 _84465 _39019 GEN_PVAR_11 s P) (@lem3600918 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600920 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term201 _84465 _39019 s P) = (term185 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600919 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600921 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600922 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term193 _84465 _39019 s P) = (term186 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600921 _84465) (@lem3600920 _84465 _39019 s P)). Qed.
Lemma lem3600923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3600924 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term202 _84465 _39019 s P) = (term203 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600923) (@lem3600922 _84465 _39019 s P)). Qed.
Lemma lem3600925 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term197 _84465 _39019 s P GEN_PVAR_11) = (term180 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term197 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600926 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term204 _84465 _39019 s P) = (term195 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600925 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600927 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600928 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term205 _84465 _39019 s P) = (term206 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600927 _84465) (@lem3600926 _84465 _39019 s P)). Qed.
Lemma lem3600929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3600930 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term207 _84465 _39019 s P) = (term208 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600929) (@lem3600928 _84465 _39019 s P)). Qed.
Lemma lem3600931 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term199 _84465 _39019 s P GEN_PVAR_11) = (term177 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term199 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3600932 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term209 _84465 _39019 s P) = (term196 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3600931 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3600933 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3600934 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term210 _84465 _39019 s P) = (term211 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600933 _84465) (@lem3600932 _84465 _39019 s P)). Qed.
Lemma lem3600935 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term194 _84465 _39019 s P) = (term212 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3600930 _84465 _39019 s P) (@lem3600934 _84465 _39019 s P)). Qed.
Lemma lem3600936 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((term193 _84465 _39019 s P) = (term194 _84465 _39019 s P)) = ((term186 _84465 _39019 s P) = (term212 _84465 _39019 s P)).
Proof. exact (MK_COMB (@lem3600924 _84465 _39019 s P) (@lem3600935 _84465 _39019 s P)). Qed.
Lemma lem3600937 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term186 _84465 _39019 s P) = (term212 _84465 _39019 s P).
Proof. exact (EQ_MP (@lem3600936 _84465 _39019 s P) (@lem3600914 _84465 _39019 s P)). Qed.
Lemma lem3601042 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term187 _84465 _39019 s) = (term213 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3600937 _84465 _39019 s P)). Qed.
Lemma lem3601043 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601044 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term188 _84465 _39019 s) = (term214 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601043 _84465) (@lem3601042 _84465 _39019 s)). Qed.
Lemma lem3601046 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3601047 {_84465 : Type'} (P : type686 _84465) (Q : type686 _84465) : (term215 _84465 P Q) = (term216 _84465 P Q).
Proof. exact (@lem3601046 (_84465 -> Prop) P Q). Qed.
Lemma lem3601048 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term217 _84465 _39019 s) = (term218 _84465 _39019 s).
Proof. exact (@lem3601047 _84465 (term219 _84465 _39019 s) (term220 _84465 _39019 s)). Qed.
Lemma lem3601049 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term221 _84465 _39019 s P) = (term206 _84465 _39019 s P).
Proof. exact (eq_refl (term221 _84465 _39019 s P)). Qed.
Lemma lem3601050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601051 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term222 _84465 _39019 s P) = (term208 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601050) (@lem3601049 _84465 _39019 s P)). Qed.
Lemma lem3601052 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term223 _84465 _39019 s P) = (term211 _84465 _39019 s P).
Proof. exact (eq_refl (term223 _84465 _39019 s P)). Qed.
Lemma lem3601053 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term224 _84465 _39019 s P) = (term212 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601051 _84465 _39019 s P) (@lem3601052 _84465 _39019 s P)). Qed.
Lemma lem3601054 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term225 _84465 _39019 s) = (term213 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3601053 _84465 _39019 s P)). Qed.
Lemma lem3601055 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601056 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term217 _84465 _39019 s) = (term214 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601055 _84465) (@lem3601054 _84465 _39019 s)). Qed.
Lemma lem3601057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601058 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term226 _84465 _39019 s) = (term227 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601057) (@lem3601056 _84465 _39019 s)). Qed.
Lemma lem3601059 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term221 _84465 _39019 s P) = (term206 _84465 _39019 s P).
Proof. exact (eq_refl (term221 _84465 _39019 s P)). Qed.
Lemma lem3601060 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term228 _84465 _39019 s) = (term219 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3601059 _84465 _39019 s P)). Qed.
Lemma lem3601061 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601062 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term229 _84465 _39019 s) = (term230 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601061 _84465) (@lem3601060 _84465 _39019 s)). Qed.
Lemma lem3601063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601064 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term231 _84465 _39019 s) = (term232 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601063) (@lem3601062 _84465 _39019 s)). Qed.
Lemma lem3601065 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term223 _84465 _39019 s P) = (term211 _84465 _39019 s P).
Proof. exact (eq_refl (term223 _84465 _39019 s P)). Qed.
Lemma lem3601066 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term233 _84465 _39019 s) = (term220 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3601065 _84465 _39019 s P)). Qed.
Lemma lem3601067 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601068 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term234 _84465 _39019 s) = (term235 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601067 _84465) (@lem3601066 _84465 _39019 s)). Qed.
Lemma lem3601069 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term218 _84465 _39019 s) = (term236 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601064 _84465 _39019 s) (@lem3601068 _84465 _39019 s)). Qed.
Lemma lem3601070 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((term217 _84465 _39019 s) = (term218 _84465 _39019 s)) = ((term214 _84465 _39019 s) = (term236 _84465 _39019 s)).
Proof. exact (MK_COMB (@lem3601058 _84465 _39019 s) (@lem3601069 _84465 _39019 s)). Qed.
Lemma lem3601071 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term214 _84465 _39019 s) = (term236 _84465 _39019 s).
Proof. exact (EQ_MP (@lem3601070 _84465 _39019 s) (@lem3601048 _84465 _39019 s)). Qed.
Lemma lem3601184 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term188 _84465 _39019 s) = (term236 _84465 _39019 s).
Proof. exact (TRANS (@lem3601044 _84465 _39019 s) (@lem3601071 _84465 _39019 s)). Qed.
Lemma lem3601185 {_84465 : Type'} (_39019 : type636 _84465) : (term189 _84465 _39019) = (term237 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601184 _84465 _39019 s)). Qed.
Lemma lem3601186 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601187 {_84465 : Type'} (_39019 : type636 _84465) : (term190 _84465 _39019) = (term238 _84465 _39019).
Proof. exact (MK_COMB (@lem3601186 _84465) (@lem3601185 _84465 _39019)). Qed.
Lemma lem3601189 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3601190 {_84465 : Type'} (P : type686 _84465) (Q : type686 _84465) : (term215 _84465 P Q) = (term216 _84465 P Q).
Proof. exact (@lem3601189 (_84465 -> Prop) P Q). Qed.
Lemma lem3601191 {_84465 : Type'} (_39019 : type636 _84465) : (term239 _84465 _39019) = (term240 _84465 _39019).
Proof. exact (@lem3601190 _84465 (term241 _84465 _39019) (term242 _84465 _39019)). Qed.
Lemma lem3601192 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term243 _84465 _39019 s) = (term230 _84465 _39019 s).
Proof. exact (eq_refl (term243 _84465 _39019 s)). Qed.
Lemma lem3601193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601194 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term244 _84465 _39019 s) = (term232 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601193) (@lem3601192 _84465 _39019 s)). Qed.
Lemma lem3601195 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term245 _84465 _39019 s) = (term235 _84465 _39019 s).
Proof. exact (eq_refl (term245 _84465 _39019 s)). Qed.
Lemma lem3601196 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term246 _84465 _39019 s) = (term236 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601194 _84465 _39019 s) (@lem3601195 _84465 _39019 s)). Qed.
Lemma lem3601197 {_84465 : Type'} (_39019 : type636 _84465) : (term247 _84465 _39019) = (term237 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601196 _84465 _39019 s)). Qed.
Lemma lem3601198 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601199 {_84465 : Type'} (_39019 : type636 _84465) : (term239 _84465 _39019) = (term238 _84465 _39019).
Proof. exact (MK_COMB (@lem3601198 _84465) (@lem3601197 _84465 _39019)). Qed.
Lemma lem3601200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601201 {_84465 : Type'} (_39019 : type636 _84465) : (term248 _84465 _39019) = (term249 _84465 _39019).
Proof. exact (MK_COMB (@lem3601200) (@lem3601199 _84465 _39019)). Qed.
Lemma lem3601202 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term243 _84465 _39019 s) = (term230 _84465 _39019 s).
Proof. exact (eq_refl (term243 _84465 _39019 s)). Qed.
Lemma lem3601203 {_84465 : Type'} (_39019 : type636 _84465) : (term250 _84465 _39019) = (term241 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601202 _84465 _39019 s)). Qed.
Lemma lem3601204 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601205 {_84465 : Type'} (_39019 : type636 _84465) : (term251 _84465 _39019) = (term252 _84465 _39019).
Proof. exact (MK_COMB (@lem3601204 _84465) (@lem3601203 _84465 _39019)). Qed.
Lemma lem3601206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601207 {_84465 : Type'} (_39019 : type636 _84465) : (term253 _84465 _39019) = (term254 _84465 _39019).
Proof. exact (MK_COMB (@lem3601206) (@lem3601205 _84465 _39019)). Qed.
Lemma lem3601208 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term245 _84465 _39019 s) = (term235 _84465 _39019 s).
Proof. exact (eq_refl (term245 _84465 _39019 s)). Qed.
Lemma lem3601209 {_84465 : Type'} (_39019 : type636 _84465) : (term255 _84465 _39019) = (term242 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601208 _84465 _39019 s)). Qed.
Lemma lem3601210 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601211 {_84465 : Type'} (_39019 : type636 _84465) : (term256 _84465 _39019) = (term257 _84465 _39019).
Proof. exact (MK_COMB (@lem3601210 _84465) (@lem3601209 _84465 _39019)). Qed.
Lemma lem3601212 {_84465 : Type'} (_39019 : type636 _84465) : (term240 _84465 _39019) = (term258 _84465 _39019).
Proof. exact (MK_COMB (@lem3601207 _84465 _39019) (@lem3601211 _84465 _39019)). Qed.
Lemma lem3601213 {_84465 : Type'} (_39019 : type636 _84465) : ((term239 _84465 _39019) = (term240 _84465 _39019)) = ((term238 _84465 _39019) = (term258 _84465 _39019)).
Proof. exact (MK_COMB (@lem3601201 _84465 _39019) (@lem3601212 _84465 _39019)). Qed.
Lemma lem3601214 {_84465 : Type'} (_39019 : type636 _84465) : (term238 _84465 _39019) = (term258 _84465 _39019).
Proof. exact (EQ_MP (@lem3601213 _84465 _39019) (@lem3601191 _84465 _39019)). Qed.
Lemma lem3601335 {_84465 : Type'} (_39019 : type636 _84465) : (term190 _84465 _39019) = (term258 _84465 _39019).
Proof. exact (TRANS (@lem3601187 _84465 _39019) (@lem3601214 _84465 _39019)). Qed.
Lemma lem3601337 {A : Type'} (P : Prop) (Q : A -> Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3601338 {_84465 : Type'} (P : Prop) (Q : _84465 -> Prop) : (term259 _84465 P Q) = (term260 _84465 P Q).
Proof. exact (@lem3601337 _84465 P Q). Qed.
Lemma lem3601339 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term261 _84465 _39019 GEN_PVAR_11 s P) = (term262 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (@lem3601338 _84465 (term263 _84465 _39019 s P GEN_PVAR_11) (term51 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3601340 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term170 _84465 GEN_PVAR_11 s P x) = (term50 _84465 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term170 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601341 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term264 _84465 GEN_PVAR_11 s P) = (term51 _84465 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3601340 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601342 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3601343 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term265 _84465 GEN_PVAR_11 s P) = (term52 _84465 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3601342 _84465) (@lem3601341 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3601344 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (GEN_PVAR_11 : _84465) : (term176 _84465 _39019 s P GEN_PVAR_11) = (term176 _84465 _39019 s P GEN_PVAR_11).
Proof. exact (eq_refl (term176 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3601345 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term261 _84465 _39019 GEN_PVAR_11 s P) = (term177 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3601344 _84465 _39019 s P GEN_PVAR_11) (@lem3601343 _84465 GEN_PVAR_11 s P)). Qed.
Lemma lem3601346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601347 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term266 _84465 _39019 GEN_PVAR_11 s P) = (term267 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3601346) (@lem3601345 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601348 {_84465 : Type'} (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term170 _84465 GEN_PVAR_11 s P x) = (term50 _84465 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term170 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601349 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (GEN_PVAR_11 : _84465) : (term176 _84465 _39019 s P GEN_PVAR_11) = (term176 _84465 _39019 s P GEN_PVAR_11).
Proof. exact (eq_refl (term176 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3601350 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term268 _84465 _39019 GEN_PVAR_11 s P x) = (term269 _84465 _39019 GEN_PVAR_11 s P x).
Proof. exact (MK_COMB (@lem3601349 _84465 _39019 s P GEN_PVAR_11) (@lem3601348 _84465 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601351 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term270 _84465 _39019 GEN_PVAR_11 s P) = (term271 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3601350 _84465 _39019 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601352 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3601353 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term262 _84465 _39019 GEN_PVAR_11 s P) = (term272 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3601352 _84465) (@lem3601351 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601354 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((term261 _84465 _39019 GEN_PVAR_11 s P) = (term262 _84465 _39019 GEN_PVAR_11 s P)) = ((term177 _84465 _39019 GEN_PVAR_11 s P) = (term272 _84465 _39019 GEN_PVAR_11 s P)).
Proof. exact (MK_COMB (@lem3601347 _84465 _39019 GEN_PVAR_11 s P) (@lem3601353 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601355 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term177 _84465 _39019 GEN_PVAR_11 s P) = (term272 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (EQ_MP (@lem3601354 _84465 _39019 GEN_PVAR_11 s P) (@lem3601339 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601356 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term196 _84465 _39019 s P) = (term273 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3601355 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601357 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3601358 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term211 _84465 _39019 s P) = (term274 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601357 _84465) (@lem3601356 _84465 _39019 s P)). Qed.
Lemma lem3601360 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3601361 {_84465 : Type'} (P : type1402 _84465) : (term277 _84465 P) = (term278 _84465 P).
Proof. exact (@lem3601360 _84465 _84465 P). Qed.
Lemma lem3601362 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term279 _84465 _39019 s P) = (term280 _84465 _39019 s P).
Proof. exact (@lem3601361 _84465 (term281 _84465 _39019 s P)). Qed.
Lemma lem3601363 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term282 _84465 _39019 s P GEN_PVAR_11) = (term271 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term282 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3601364 {_84465 : Type'} (x : _84465) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3601365 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term283 _84465 _39019 s P GEN_PVAR_11 x) = (term284 _84465 _39019 GEN_PVAR_11 s P x).
Proof. exact (MK_COMB (@lem3601363 _84465 _39019 GEN_PVAR_11 s P) (@lem3601364 _84465 x)). Qed.
Lemma lem3601366 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term284 _84465 _39019 GEN_PVAR_11 s P x) = (term269 _84465 _39019 GEN_PVAR_11 s P x).
Proof. exact (eq_refl (term284 _84465 _39019 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601367 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465) : (term283 _84465 _39019 s P GEN_PVAR_11 x) = (term269 _84465 _39019 GEN_PVAR_11 s P x).
Proof. exact (TRANS (@lem3601365 _84465 _39019 GEN_PVAR_11 s P x) (@lem3601366 _84465 _39019 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601368 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term285 _84465 _39019 s P GEN_PVAR_11) = (term271 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (fun_ext (fun x : _84465 => @lem3601367 _84465 _39019 GEN_PVAR_11 s P x)). Qed.
Lemma lem3601369 {_84465 : Type'} : (@ex _84465) = (@ex _84465).
Proof. exact (eq_refl (@ex _84465)). Qed.
Lemma lem3601370 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term286 _84465 _39019 s P GEN_PVAR_11) = (term272 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (MK_COMB (@lem3601369 _84465) (@lem3601368 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601371 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term287 _84465 _39019 s P) = (term273 _84465 _39019 s P).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3601370 _84465 _39019 GEN_PVAR_11 s P)). Qed.
Lemma lem3601372 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3601373 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term279 _84465 _39019 s P) = (term274 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601372 _84465) (@lem3601371 _84465 _39019 s P)). Qed.
Lemma lem3601374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601375 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term288 _84465 _39019 s P) = (term289 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601374) (@lem3601373 _84465 _39019 s P)). Qed.
Lemma lem3601376 {_84465 : Type'} (_39019 : type636 _84465) (GEN_PVAR_11 : _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term282 _84465 _39019 s P GEN_PVAR_11) = (term271 _84465 _39019 GEN_PVAR_11 s P).
Proof. exact (eq_refl (term282 _84465 _39019 s P GEN_PVAR_11)). Qed.
Lemma lem3601377 {_84465 : Type'} (x : _84465 -> _84465) (GEN_PVAR_11 : _84465) : (x GEN_PVAR_11) = (x GEN_PVAR_11).
Proof. exact (eq_refl (x GEN_PVAR_11)). Qed.
Lemma lem3601378 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) (GEN_PVAR_11 : _84465) : (term290 _84465 _39019 s P x GEN_PVAR_11) = (term291 _84465 _39019 s P x GEN_PVAR_11).
Proof. exact (MK_COMB (@lem3601376 _84465 _39019 GEN_PVAR_11 s P) (@lem3601377 _84465 x GEN_PVAR_11)). Qed.
Lemma lem3601379 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) (GEN_PVAR_11 : _84465) : (term291 _84465 _39019 s P x GEN_PVAR_11) = (term292 _84465 _39019 s P x GEN_PVAR_11).
Proof. exact (eq_refl (term291 _84465 _39019 s P x GEN_PVAR_11)). Qed.
Lemma lem3601380 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) (GEN_PVAR_11 : _84465) : (term290 _84465 _39019 s P x GEN_PVAR_11) = (term292 _84465 _39019 s P x GEN_PVAR_11).
Proof. exact (TRANS (@lem3601378 _84465 _39019 s P x GEN_PVAR_11) (@lem3601379 _84465 _39019 s P x GEN_PVAR_11)). Qed.
Lemma lem3601381 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) : (term293 _84465 _39019 s P x) = (term294 _84465 _39019 s P x).
Proof. exact (fun_ext (fun GEN_PVAR_11 : _84465 => @lem3601380 _84465 _39019 s P x GEN_PVAR_11)). Qed.
Lemma lem3601382 {_84465 : Type'} : (@all _84465) = (@all _84465).
Proof. exact (eq_refl (@all _84465)). Qed.
Lemma lem3601383 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) : (term295 _84465 _39019 s P x) = (term296 _84465 _39019 s P x).
Proof. exact (MK_COMB (@lem3601382 _84465) (@lem3601381 _84465 _39019 s P x)). Qed.
Lemma lem3601384 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term297 _84465 _39019 s P) = (term298 _84465 _39019 s P).
Proof. exact (fun_ext (fun x : _84465 -> _84465 => @lem3601383 _84465 _39019 s P x)). Qed.
Lemma lem3601385 {_84465 : Type'} : (@ex (_84465 -> _84465)) = (@ex (_84465 -> _84465)).
Proof. exact (eq_refl (@ex (_84465 -> _84465))). Qed.
Lemma lem3601386 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term280 _84465 _39019 s P) = (term299 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601385 _84465) (@lem3601384 _84465 _39019 s P)). Qed.
Lemma lem3601387 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : ((term279 _84465 _39019 s P) = (term280 _84465 _39019 s P)) = ((term274 _84465 _39019 s P) = (term299 _84465 _39019 s P)).
Proof. exact (MK_COMB (@lem3601375 _84465 _39019 s P) (@lem3601386 _84465 _39019 s P)). Qed.
Lemma lem3601388 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term274 _84465 _39019 s P) = (term299 _84465 _39019 s P).
Proof. exact (EQ_MP (@lem3601387 _84465 _39019 s P) (@lem3601362 _84465 _39019 s P)). Qed.
Lemma lem3601389 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term211 _84465 _39019 s P) = (term299 _84465 _39019 s P).
Proof. exact (TRANS (@lem3601358 _84465 _39019 s P) (@lem3601388 _84465 _39019 s P)). Qed.
Lemma lem3601390 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term220 _84465 _39019 s) = (term300 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3601389 _84465 _39019 s P)). Qed.
Lemma lem3601391 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601392 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term235 _84465 _39019 s) = (term301 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601391 _84465) (@lem3601390 _84465 _39019 s)). Qed.
Lemma lem3601394 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3601395 {_84465 : Type'} (P : type624 _84465) : (term302 _84465 P) = (term303 _84465 P).
Proof. exact (@lem3601394 (_84465 -> Prop) (_84465 -> _84465) P). Qed.
Lemma lem3601396 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term304 _84465 _39019 s) = (term305 _84465 _39019 s).
Proof. exact (@lem3601395 _84465 (term306 _84465 _39019 s)). Qed.
Lemma lem3601397 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term307 _84465 _39019 s P) = (term298 _84465 _39019 s P).
Proof. exact (eq_refl (term307 _84465 _39019 s P)). Qed.
Lemma lem3601398 {_84465 : Type'} (x : _84465 -> _84465) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3601399 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) : (term308 _84465 _39019 s P x) = (term309 _84465 _39019 s P x).
Proof. exact (MK_COMB (@lem3601397 _84465 _39019 s P) (@lem3601398 _84465 x)). Qed.
Lemma lem3601400 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) : (term309 _84465 _39019 s P x) = (term296 _84465 _39019 s P x).
Proof. exact (eq_refl (term309 _84465 _39019 s P x)). Qed.
Lemma lem3601401 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) (x : _84465 -> _84465) : (term308 _84465 _39019 s P x) = (term296 _84465 _39019 s P x).
Proof. exact (TRANS (@lem3601399 _84465 _39019 s P x) (@lem3601400 _84465 _39019 s P x)). Qed.
Lemma lem3601402 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term310 _84465 _39019 s P) = (term298 _84465 _39019 s P).
Proof. exact (fun_ext (fun x : _84465 -> _84465 => @lem3601401 _84465 _39019 s P x)). Qed.
Lemma lem3601403 {_84465 : Type'} : (@ex (_84465 -> _84465)) = (@ex (_84465 -> _84465)).
Proof. exact (eq_refl (@ex (_84465 -> _84465))). Qed.
Lemma lem3601404 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term311 _84465 _39019 s P) = (term299 _84465 _39019 s P).
Proof. exact (MK_COMB (@lem3601403 _84465) (@lem3601402 _84465 _39019 s P)). Qed.
Lemma lem3601405 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term312 _84465 _39019 s) = (term300 _84465 _39019 s).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3601404 _84465 _39019 s P)). Qed.
Lemma lem3601406 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601407 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term304 _84465 _39019 s) = (term301 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601406 _84465) (@lem3601405 _84465 _39019 s)). Qed.
Lemma lem3601408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601409 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term313 _84465 _39019 s) = (term314 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601408) (@lem3601407 _84465 _39019 s)). Qed.
Lemma lem3601410 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (P : _84465 -> Prop) : (term307 _84465 _39019 s P) = (term298 _84465 _39019 s P).
Proof. exact (eq_refl (term307 _84465 _39019 s P)). Qed.
Lemma lem3601411 {_84465 : Type'} (x : type670 _84465) (P : _84465 -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem3601412 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) (P : _84465 -> Prop) : (term315 _84465 _39019 s x P) = (term316 _84465 _39019 s x P).
Proof. exact (MK_COMB (@lem3601410 _84465 _39019 s P) (@lem3601411 _84465 x P)). Qed.
Lemma lem3601413 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) (P : _84465 -> Prop) : (term316 _84465 _39019 s x P) = (term317 _84465 _39019 s x P).
Proof. exact (eq_refl (term316 _84465 _39019 s x P)). Qed.
Lemma lem3601414 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) (P : _84465 -> Prop) : (term315 _84465 _39019 s x P) = (term317 _84465 _39019 s x P).
Proof. exact (TRANS (@lem3601412 _84465 _39019 s x P) (@lem3601413 _84465 _39019 s x P)). Qed.
Lemma lem3601415 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) : (term318 _84465 _39019 s x) = (term319 _84465 _39019 s x).
Proof. exact (fun_ext (fun P : _84465 -> Prop => @lem3601414 _84465 _39019 s x P)). Qed.
Lemma lem3601416 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601417 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) : (term320 _84465 _39019 s x) = (term321 _84465 _39019 s x).
Proof. exact (MK_COMB (@lem3601416 _84465) (@lem3601415 _84465 _39019 s x)). Qed.
Lemma lem3601418 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term322 _84465 _39019 s) = (term323 _84465 _39019 s).
Proof. exact (fun_ext (fun x : type670 _84465 => @lem3601417 _84465 _39019 s x)). Qed.
Lemma lem3601419 {_84465 : Type'} : (@ex ((_84465 -> Prop) -> _84465 -> _84465)) = (@ex ((_84465 -> Prop) -> _84465 -> _84465)).
Proof. exact (eq_refl (@ex ((_84465 -> Prop) -> _84465 -> _84465))). Qed.
Lemma lem3601420 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term305 _84465 _39019 s) = (term324 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601419 _84465) (@lem3601418 _84465 _39019 s)). Qed.
Lemma lem3601421 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : ((term304 _84465 _39019 s) = (term305 _84465 _39019 s)) = ((term301 _84465 _39019 s) = (term324 _84465 _39019 s)).
Proof. exact (MK_COMB (@lem3601409 _84465 _39019 s) (@lem3601420 _84465 _39019 s)). Qed.
Lemma lem3601422 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term301 _84465 _39019 s) = (term324 _84465 _39019 s).
Proof. exact (EQ_MP (@lem3601421 _84465 _39019 s) (@lem3601396 _84465 _39019 s)). Qed.
Lemma lem3601423 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term235 _84465 _39019 s) = (term324 _84465 _39019 s).
Proof. exact (TRANS (@lem3601392 _84465 _39019 s) (@lem3601422 _84465 _39019 s)). Qed.
Lemma lem3601424 {_84465 : Type'} (_39019 : type636 _84465) : (term242 _84465 _39019) = (term325 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601423 _84465 _39019 s)). Qed.
Lemma lem3601425 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601426 {_84465 : Type'} (_39019 : type636 _84465) : (term257 _84465 _39019) = (term326 _84465 _39019).
Proof. exact (MK_COMB (@lem3601425 _84465) (@lem3601424 _84465 _39019)). Qed.
Lemma lem3601428 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3601429 {_84465 : Type'} (P : type595 _84465) : (term327 _84465 P) = (term328 _84465 P).
Proof. exact (@lem3601428 (_84465 -> Prop) (type670 _84465) P). Qed.
Lemma lem3601430 {_84465 : Type'} (_39019 : type636 _84465) : (term329 _84465 _39019) = (term330 _84465 _39019).
Proof. exact (@lem3601429 _84465 (term331 _84465 _39019)). Qed.
Lemma lem3601431 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term332 _84465 _39019 s) = (term323 _84465 _39019 s).
Proof. exact (eq_refl (term332 _84465 _39019 s)). Qed.
Lemma lem3601432 {_84465 : Type'} (x : type670 _84465) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3601433 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) : (term333 _84465 _39019 s x) = (term334 _84465 _39019 s x).
Proof. exact (MK_COMB (@lem3601431 _84465 _39019 s) (@lem3601432 _84465 x)). Qed.
Lemma lem3601434 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) : (term334 _84465 _39019 s x) = (term321 _84465 _39019 s x).
Proof. exact (eq_refl (term334 _84465 _39019 s x)). Qed.
Lemma lem3601435 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) (x : type670 _84465) : (term333 _84465 _39019 s x) = (term321 _84465 _39019 s x).
Proof. exact (TRANS (@lem3601433 _84465 _39019 s x) (@lem3601434 _84465 _39019 s x)). Qed.
Lemma lem3601436 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term335 _84465 _39019 s) = (term323 _84465 _39019 s).
Proof. exact (fun_ext (fun x : type670 _84465 => @lem3601435 _84465 _39019 s x)). Qed.
Lemma lem3601437 {_84465 : Type'} : (@ex ((_84465 -> Prop) -> _84465 -> _84465)) = (@ex ((_84465 -> Prop) -> _84465 -> _84465)).
Proof. exact (eq_refl (@ex ((_84465 -> Prop) -> _84465 -> _84465))). Qed.
Lemma lem3601438 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term336 _84465 _39019 s) = (term324 _84465 _39019 s).
Proof. exact (MK_COMB (@lem3601437 _84465) (@lem3601436 _84465 _39019 s)). Qed.
Lemma lem3601439 {_84465 : Type'} (_39019 : type636 _84465) : (term337 _84465 _39019) = (term325 _84465 _39019).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601438 _84465 _39019 s)). Qed.
Lemma lem3601440 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601441 {_84465 : Type'} (_39019 : type636 _84465) : (term329 _84465 _39019) = (term326 _84465 _39019).
Proof. exact (MK_COMB (@lem3601440 _84465) (@lem3601439 _84465 _39019)). Qed.
Lemma lem3601442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601443 {_84465 : Type'} (_39019 : type636 _84465) : (term338 _84465 _39019) = (term339 _84465 _39019).
Proof. exact (MK_COMB (@lem3601442) (@lem3601441 _84465 _39019)). Qed.
Lemma lem3601444 {_84465 : Type'} (_39019 : type636 _84465) (s : _84465 -> Prop) : (term332 _84465 _39019 s) = (term323 _84465 _39019 s).
Proof. exact (eq_refl (term332 _84465 _39019 s)). Qed.
Lemma lem3601445 {_84465 : Type'} (x : type635 _84465) (s : _84465 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3601446 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) (s : _84465 -> Prop) : (term340 _84465 _39019 x s) = (term341 _84465 _39019 x s).
Proof. exact (MK_COMB (@lem3601444 _84465 _39019 s) (@lem3601445 _84465 x s)). Qed.
Lemma lem3601447 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) (s : _84465 -> Prop) : (term341 _84465 _39019 x s) = (term342 _84465 _39019 x s).
Proof. exact (eq_refl (term341 _84465 _39019 x s)). Qed.
Lemma lem3601448 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) (s : _84465 -> Prop) : (term340 _84465 _39019 x s) = (term342 _84465 _39019 x s).
Proof. exact (TRANS (@lem3601446 _84465 _39019 x s) (@lem3601447 _84465 _39019 x s)). Qed.
Lemma lem3601449 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) : (term343 _84465 _39019 x) = (term344 _84465 _39019 x).
Proof. exact (fun_ext (fun s : _84465 -> Prop => @lem3601448 _84465 _39019 x s)). Qed.
Lemma lem3601450 {_84465 : Type'} : (@all (_84465 -> Prop)) = (@all (_84465 -> Prop)).
Proof. exact (eq_refl (@all (_84465 -> Prop))). Qed.
Lemma lem3601451 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) : (term345 _84465 _39019 x) = (term346 _84465 _39019 x).
Proof. exact (MK_COMB (@lem3601450 _84465) (@lem3601449 _84465 _39019 x)). Qed.
Lemma lem3601452 {_84465 : Type'} (_39019 : type636 _84465) : (term347 _84465 _39019) = (term348 _84465 _39019).
Proof. exact (fun_ext (fun x : type635 _84465 => @lem3601451 _84465 _39019 x)). Qed.
Lemma lem3601453 {_84465 : Type'} : (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465)) = (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465)).
Proof. exact (eq_refl (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465))). Qed.
Lemma lem3601454 {_84465 : Type'} (_39019 : type636 _84465) : (term330 _84465 _39019) = (term349 _84465 _39019).
Proof. exact (MK_COMB (@lem3601453 _84465) (@lem3601452 _84465 _39019)). Qed.
Lemma lem3601455 {_84465 : Type'} (_39019 : type636 _84465) : ((term329 _84465 _39019) = (term330 _84465 _39019)) = ((term326 _84465 _39019) = (term349 _84465 _39019)).
Proof. exact (MK_COMB (@lem3601443 _84465 _39019) (@lem3601454 _84465 _39019)). Qed.
Lemma lem3601456 {_84465 : Type'} (_39019 : type636 _84465) : (term326 _84465 _39019) = (term349 _84465 _39019).
Proof. exact (EQ_MP (@lem3601455 _84465 _39019) (@lem3601430 _84465 _39019)). Qed.
Lemma lem3601457 {_84465 : Type'} (_39019 : type636 _84465) : (term257 _84465 _39019) = (term349 _84465 _39019).
Proof. exact (TRANS (@lem3601426 _84465 _39019) (@lem3601456 _84465 _39019)). Qed.
Lemma lem3601458 {_84465 : Type'} (_39019 : type636 _84465) : (term254 _84465 _39019) = (term254 _84465 _39019).
Proof. exact (eq_refl (term254 _84465 _39019)). Qed.
Lemma lem3601459 {_84465 : Type'} (_39019 : type636 _84465) : (term258 _84465 _39019) = (term350 _84465 _39019).
Proof. exact (MK_COMB (@lem3601458 _84465 _39019) (@lem3601457 _84465 _39019)). Qed.
Lemma lem3601461 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3601462 {_84465 : Type'} (P : Prop) (Q : type137 _84465) : (term353 _84465 P Q) = (term354 _84465 P Q).
Proof. exact (@lem3601461 (type635 _84465) P Q). Qed.
Lemma lem3601463 {_84465 : Type'} (_39019 : type636 _84465) : (term355 _84465 _39019) = (term356 _84465 _39019).
Proof. exact (@lem3601462 _84465 (term252 _84465 _39019) (term348 _84465 _39019)). Qed.
Lemma lem3601464 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) : (term357 _84465 _39019 x) = (term346 _84465 _39019 x).
Proof. exact (eq_refl (term357 _84465 _39019 x)). Qed.
Lemma lem3601465 {_84465 : Type'} (_39019 : type636 _84465) : (term358 _84465 _39019) = (term348 _84465 _39019).
Proof. exact (fun_ext (fun x : type635 _84465 => @lem3601464 _84465 _39019 x)). Qed.
Lemma lem3601466 {_84465 : Type'} : (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465)) = (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465)).
Proof. exact (eq_refl (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465))). Qed.
Lemma lem3601467 {_84465 : Type'} (_39019 : type636 _84465) : (term359 _84465 _39019) = (term349 _84465 _39019).
Proof. exact (MK_COMB (@lem3601466 _84465) (@lem3601465 _84465 _39019)). Qed.
Lemma lem3601468 {_84465 : Type'} (_39019 : type636 _84465) : (term254 _84465 _39019) = (term254 _84465 _39019).
Proof. exact (eq_refl (term254 _84465 _39019)). Qed.
Lemma lem3601469 {_84465 : Type'} (_39019 : type636 _84465) : (term355 _84465 _39019) = (term350 _84465 _39019).
Proof. exact (MK_COMB (@lem3601468 _84465 _39019) (@lem3601467 _84465 _39019)). Qed.
Lemma lem3601470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601471 {_84465 : Type'} (_39019 : type636 _84465) : (term360 _84465 _39019) = (term361 _84465 _39019).
Proof. exact (MK_COMB (@lem3601470) (@lem3601469 _84465 _39019)). Qed.
Lemma lem3601472 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) : (term357 _84465 _39019 x) = (term346 _84465 _39019 x).
Proof. exact (eq_refl (term357 _84465 _39019 x)). Qed.
Lemma lem3601473 {_84465 : Type'} (_39019 : type636 _84465) : (term254 _84465 _39019) = (term254 _84465 _39019).
Proof. exact (eq_refl (term254 _84465 _39019)). Qed.
Lemma lem3601474 {_84465 : Type'} (_39019 : type636 _84465) (x : type635 _84465) : (term362 _84465 _39019 x) = (term363 _84465 _39019 x).
Proof. exact (MK_COMB (@lem3601473 _84465 _39019) (@lem3601472 _84465 _39019 x)). Qed.
Lemma lem3601475 {_84465 : Type'} (_39019 : type636 _84465) : (term364 _84465 _39019) = (term365 _84465 _39019).
Proof. exact (fun_ext (fun x : type635 _84465 => @lem3601474 _84465 _39019 x)). Qed.
Lemma lem3601476 {_84465 : Type'} : (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465)) = (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465)).
Proof. exact (eq_refl (@ex ((_84465 -> Prop) -> (_84465 -> Prop) -> _84465 -> _84465))). Qed.
Lemma lem3601477 {_84465 : Type'} (_39019 : type636 _84465) : (term356 _84465 _39019) = (term366 _84465 _39019).
Proof. exact (MK_COMB (@lem3601476 _84465) (@lem3601475 _84465 _39019)). Qed.
Lemma lem3601478 {_84465 : Type'} (_39019 : type636 _84465) : ((term355 _84465 _39019) = (term356 _84465 _39019)) = ((term350 _84465 _39019) = (term366 _84465 _39019)).
Proof. exact (MK_COMB (@lem3601471 _84465 _39019) (@lem3601477 _84465 _39019)). Qed.
Lemma lem3601479 {_84465 : Type'} (_39019 : type636 _84465) : (term350 _84465 _39019) = (term366 _84465 _39019).
Proof. exact (EQ_MP (@lem3601478 _84465 _39019) (@lem3601463 _84465 _39019)). Qed.
Lemma lem3601480 {_84465 : Type'} (_39019 : type636 _84465) : (term258 _84465 _39019) = (term366 _84465 _39019).
Proof. exact (TRANS (@lem3601459 _84465 _39019) (@lem3601479 _84465 _39019)). Qed.
Lemma lem3601481 {_84465 : Type'} (_39019 : type636 _84465) : (term190 _84465 _39019) = (term366 _84465 _39019).
Proof. exact (TRANS (@lem3601335 _84465 _39019) (@lem3601480 _84465 _39019)). Qed.
Lemma lem3601482 {_84465 : Type'} (_39019 : type636 _84465) : (term131 _84465 _39019) = (term366 _84465 _39019).
Proof. exact (TRANS (@lem3600902 _84465 _39019) (@lem3601481 _84465 _39019)). Qed.
Lemma lem3601483 {_84465 : Type'} (_39019 : type636 _84465) (h1 : term131 _84465 _39019) : term366 _84465 _39019.
Proof. exact (EQ_MP (@lem3601482 _84465 _39019) (@lem3600859 _84465 _39019 h1)). Qed.
Lemma lem3601487 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term50 A GEN_PVAR_91 s P x) = (term50 A GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term50 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601488 {A : Type'} (P : A -> Prop) : (term166 A P) = (term167 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3601489 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term168 A GEN_PVAR_91 s P) = (term169 A GEN_PVAR_91 s P).
Proof. exact (@lem3601488 A (term51 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601490 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term170 A GEN_PVAR_91 s P x) = (term50 A GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term170 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3601493 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term171 A GEN_PVAR_91 s P x) = (term172 A GEN_PVAR_91 s P x).
Proof. exact (MK_COMB (@lem3601491) (@lem3601490 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601494 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term173 A GEN_PVAR_91 s P) = (term174 A GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3601493 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601496 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term169 A GEN_PVAR_91 s P) = (term175 A GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601495 A) (@lem3601494 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601497 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term168 A GEN_PVAR_91 s P) = (term175 A GEN_PVAR_91 s P).
Proof. exact (TRANS (@lem3601489 A GEN_PVAR_91 s P) (@lem3601496 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601498 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term51 A GEN_PVAR_91 s P) = (term51 A GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3601487 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601499 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3601500 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term52 A GEN_PVAR_91 s P) = (term52 A GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601499 A) (@lem3601498 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601502 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term176 A _39018 s P GEN_PVAR_91) = (term176 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term176 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601503 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term177 A _39018 GEN_PVAR_91 s P) = (term177 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601502 A _39018 s P GEN_PVAR_91) (@lem3601500 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601505 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term178 A _39018 s P GEN_PVAR_91) = (term178 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term178 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601506 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term179 A _39018 GEN_PVAR_91 s P) = (term180 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601505 A _39018 s P GEN_PVAR_91) (@lem3601497 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601508 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term181 A _39018 GEN_PVAR_91 s P) = (term182 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601507) (@lem3601506 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601509 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term183 A _39018 GEN_PVAR_91 s P) = (term184 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601508 A _39018 GEN_PVAR_91 s P) (@lem3601503 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601510 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)) = (term183 A _39018 GEN_PVAR_91 s P).
Proof. exact (@lem17784 (_39018 s P GEN_PVAR_91) (term52 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601511 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((_39018 s P GEN_PVAR_91) = (term52 A GEN_PVAR_91 s P)) = (term184 A _39018 GEN_PVAR_91 s P).
Proof. exact (TRANS (@lem3601510 A _39018 GEN_PVAR_91 s P) (@lem3601509 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601512 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term126 A _39018 s P) = (term185 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601511 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601514 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term127 A _39018 s P) = (term186 A _39018 s P).
Proof. exact (MK_COMB (@lem3601513 A) (@lem3601512 A _39018 s P)). Qed.
Lemma lem3601515 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term128 A _39018 s) = (term187 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3601514 A _39018 s P)). Qed.
Lemma lem3601516 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601517 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term129 A _39018 s) = (term188 A _39018 s).
Proof. exact (MK_COMB (@lem3601516 A) (@lem3601515 A _39018 s)). Qed.
Lemma lem3601518 {A : Type'} (_39018 : type636 A) : (term130 A _39018) = (term189 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3601517 A _39018 s)). Qed.
Lemma lem3601519 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601520 {A : Type'} (_39018 : type636 A) : (term131 A _39018) = (term190 A _39018).
Proof. exact (MK_COMB (@lem3601519 A) (@lem3601518 A _39018)). Qed.
Lemma lem3601530 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3601531 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (@lem3601530 A P Q). Qed.
Lemma lem3601532 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term193 A _39018 s P) = (term194 A _39018 s P).
Proof. exact (@lem3601531 A (term195 A _39018 s P) (term196 A _39018 s P)). Qed.
Lemma lem3601533 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term197 A _39018 s P GEN_PVAR_91) = (term180 A _39018 GEN_PVAR_91 s P).
Proof. exact (eq_refl (term197 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601535 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term198 A _39018 s P GEN_PVAR_91) = (term182 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601534) (@lem3601533 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601536 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term199 A _39018 s P GEN_PVAR_91) = (term177 A _39018 GEN_PVAR_91 s P).
Proof. exact (eq_refl (term199 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601537 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term200 A _39018 s P GEN_PVAR_91) = (term184 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601535 A _39018 GEN_PVAR_91 s P) (@lem3601536 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601538 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term201 A _39018 s P) = (term185 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601537 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601540 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term193 A _39018 s P) = (term186 A _39018 s P).
Proof. exact (MK_COMB (@lem3601539 A) (@lem3601538 A _39018 s P)). Qed.
Lemma lem3601541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601542 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term202 A _39018 s P) = (term203 A _39018 s P).
Proof. exact (MK_COMB (@lem3601541) (@lem3601540 A _39018 s P)). Qed.
Lemma lem3601543 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term197 A _39018 s P GEN_PVAR_91) = (term180 A _39018 GEN_PVAR_91 s P).
Proof. exact (eq_refl (term197 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601544 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term204 A _39018 s P) = (term195 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601543 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601546 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term205 A _39018 s P) = (term206 A _39018 s P).
Proof. exact (MK_COMB (@lem3601545 A) (@lem3601544 A _39018 s P)). Qed.
Lemma lem3601547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601548 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term207 A _39018 s P) = (term208 A _39018 s P).
Proof. exact (MK_COMB (@lem3601547) (@lem3601546 A _39018 s P)). Qed.
Lemma lem3601549 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term199 A _39018 s P GEN_PVAR_91) = (term177 A _39018 GEN_PVAR_91 s P).
Proof. exact (eq_refl (term199 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601550 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term209 A _39018 s P) = (term196 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601549 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601552 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term210 A _39018 s P) = (term211 A _39018 s P).
Proof. exact (MK_COMB (@lem3601551 A) (@lem3601550 A _39018 s P)). Qed.
Lemma lem3601553 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term194 A _39018 s P) = (term212 A _39018 s P).
Proof. exact (MK_COMB (@lem3601548 A _39018 s P) (@lem3601552 A _39018 s P)). Qed.
Lemma lem3601554 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((term193 A _39018 s P) = (term194 A _39018 s P)) = ((term186 A _39018 s P) = (term212 A _39018 s P)).
Proof. exact (MK_COMB (@lem3601542 A _39018 s P) (@lem3601553 A _39018 s P)). Qed.
Lemma lem3601555 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term186 A _39018 s P) = (term212 A _39018 s P).
Proof. exact (EQ_MP (@lem3601554 A _39018 s P) (@lem3601532 A _39018 s P)). Qed.
Lemma lem3601660 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term187 A _39018 s) = (term213 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3601555 A _39018 s P)). Qed.
Lemma lem3601661 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601662 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term188 A _39018 s) = (term214 A _39018 s).
Proof. exact (MK_COMB (@lem3601661 A) (@lem3601660 A _39018 s)). Qed.
Lemma lem3601664 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3601665 {A : Type'} (P : type686 A) (Q : type686 A) : (term215 A P Q) = (term216 A P Q).
Proof. exact (@lem3601664 (A -> Prop) P Q). Qed.
Lemma lem3601666 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term217 A _39018 s) = (term218 A _39018 s).
Proof. exact (@lem3601665 A (term219 A _39018 s) (term220 A _39018 s)). Qed.
Lemma lem3601667 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term221 A _39018 s P) = (term206 A _39018 s P).
Proof. exact (eq_refl (term221 A _39018 s P)). Qed.
Lemma lem3601668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601669 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term222 A _39018 s P) = (term208 A _39018 s P).
Proof. exact (MK_COMB (@lem3601668) (@lem3601667 A _39018 s P)). Qed.
Lemma lem3601670 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term223 A _39018 s P) = (term211 A _39018 s P).
Proof. exact (eq_refl (term223 A _39018 s P)). Qed.
Lemma lem3601671 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term224 A _39018 s P) = (term212 A _39018 s P).
Proof. exact (MK_COMB (@lem3601669 A _39018 s P) (@lem3601670 A _39018 s P)). Qed.
Lemma lem3601672 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term225 A _39018 s) = (term213 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3601671 A _39018 s P)). Qed.
Lemma lem3601673 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601674 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term217 A _39018 s) = (term214 A _39018 s).
Proof. exact (MK_COMB (@lem3601673 A) (@lem3601672 A _39018 s)). Qed.
Lemma lem3601675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601676 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term226 A _39018 s) = (term227 A _39018 s).
Proof. exact (MK_COMB (@lem3601675) (@lem3601674 A _39018 s)). Qed.
Lemma lem3601677 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term221 A _39018 s P) = (term206 A _39018 s P).
Proof. exact (eq_refl (term221 A _39018 s P)). Qed.
Lemma lem3601678 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term228 A _39018 s) = (term219 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3601677 A _39018 s P)). Qed.
Lemma lem3601679 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601680 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term229 A _39018 s) = (term230 A _39018 s).
Proof. exact (MK_COMB (@lem3601679 A) (@lem3601678 A _39018 s)). Qed.
Lemma lem3601681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601682 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term231 A _39018 s) = (term232 A _39018 s).
Proof. exact (MK_COMB (@lem3601681) (@lem3601680 A _39018 s)). Qed.
Lemma lem3601683 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term223 A _39018 s P) = (term211 A _39018 s P).
Proof. exact (eq_refl (term223 A _39018 s P)). Qed.
Lemma lem3601684 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term233 A _39018 s) = (term220 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3601683 A _39018 s P)). Qed.
Lemma lem3601685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601686 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term234 A _39018 s) = (term235 A _39018 s).
Proof. exact (MK_COMB (@lem3601685 A) (@lem3601684 A _39018 s)). Qed.
Lemma lem3601687 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term218 A _39018 s) = (term236 A _39018 s).
Proof. exact (MK_COMB (@lem3601682 A _39018 s) (@lem3601686 A _39018 s)). Qed.
Lemma lem3601688 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((term217 A _39018 s) = (term218 A _39018 s)) = ((term214 A _39018 s) = (term236 A _39018 s)).
Proof. exact (MK_COMB (@lem3601676 A _39018 s) (@lem3601687 A _39018 s)). Qed.
Lemma lem3601689 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term214 A _39018 s) = (term236 A _39018 s).
Proof. exact (EQ_MP (@lem3601688 A _39018 s) (@lem3601666 A _39018 s)). Qed.
Lemma lem3601802 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term188 A _39018 s) = (term236 A _39018 s).
Proof. exact (TRANS (@lem3601662 A _39018 s) (@lem3601689 A _39018 s)). Qed.
Lemma lem3601803 {A : Type'} (_39018 : type636 A) : (term189 A _39018) = (term237 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3601802 A _39018 s)). Qed.
Lemma lem3601804 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601805 {A : Type'} (_39018 : type636 A) : (term190 A _39018) = (term238 A _39018).
Proof. exact (MK_COMB (@lem3601804 A) (@lem3601803 A _39018)). Qed.
Lemma lem3601807 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3601808 {A : Type'} (P : type686 A) (Q : type686 A) : (term215 A P Q) = (term216 A P Q).
Proof. exact (@lem3601807 (A -> Prop) P Q). Qed.
Lemma lem3601809 {A : Type'} (_39018 : type636 A) : (term239 A _39018) = (term240 A _39018).
Proof. exact (@lem3601808 A (term241 A _39018) (term242 A _39018)). Qed.
Lemma lem3601810 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term243 A _39018 s) = (term230 A _39018 s).
Proof. exact (eq_refl (term243 A _39018 s)). Qed.
Lemma lem3601811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601812 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term244 A _39018 s) = (term232 A _39018 s).
Proof. exact (MK_COMB (@lem3601811) (@lem3601810 A _39018 s)). Qed.
Lemma lem3601813 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term245 A _39018 s) = (term235 A _39018 s).
Proof. exact (eq_refl (term245 A _39018 s)). Qed.
Lemma lem3601814 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term246 A _39018 s) = (term236 A _39018 s).
Proof. exact (MK_COMB (@lem3601812 A _39018 s) (@lem3601813 A _39018 s)). Qed.
Lemma lem3601815 {A : Type'} (_39018 : type636 A) : (term247 A _39018) = (term237 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3601814 A _39018 s)). Qed.
Lemma lem3601816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601817 {A : Type'} (_39018 : type636 A) : (term239 A _39018) = (term238 A _39018).
Proof. exact (MK_COMB (@lem3601816 A) (@lem3601815 A _39018)). Qed.
Lemma lem3601818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601819 {A : Type'} (_39018 : type636 A) : (term248 A _39018) = (term249 A _39018).
Proof. exact (MK_COMB (@lem3601818) (@lem3601817 A _39018)). Qed.
Lemma lem3601820 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term243 A _39018 s) = (term230 A _39018 s).
Proof. exact (eq_refl (term243 A _39018 s)). Qed.
Lemma lem3601821 {A : Type'} (_39018 : type636 A) : (term250 A _39018) = (term241 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3601820 A _39018 s)). Qed.
Lemma lem3601822 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601823 {A : Type'} (_39018 : type636 A) : (term251 A _39018) = (term252 A _39018).
Proof. exact (MK_COMB (@lem3601822 A) (@lem3601821 A _39018)). Qed.
Lemma lem3601824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3601825 {A : Type'} (_39018 : type636 A) : (term253 A _39018) = (term254 A _39018).
Proof. exact (MK_COMB (@lem3601824) (@lem3601823 A _39018)). Qed.
Lemma lem3601826 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term245 A _39018 s) = (term235 A _39018 s).
Proof. exact (eq_refl (term245 A _39018 s)). Qed.
Lemma lem3601827 {A : Type'} (_39018 : type636 A) : (term255 A _39018) = (term242 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3601826 A _39018 s)). Qed.
Lemma lem3601828 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3601829 {A : Type'} (_39018 : type636 A) : (term256 A _39018) = (term257 A _39018).
Proof. exact (MK_COMB (@lem3601828 A) (@lem3601827 A _39018)). Qed.
Lemma lem3601830 {A : Type'} (_39018 : type636 A) : (term240 A _39018) = (term258 A _39018).
Proof. exact (MK_COMB (@lem3601825 A _39018) (@lem3601829 A _39018)). Qed.
Lemma lem3601831 {A : Type'} (_39018 : type636 A) : ((term239 A _39018) = (term240 A _39018)) = ((term238 A _39018) = (term258 A _39018)).
Proof. exact (MK_COMB (@lem3601819 A _39018) (@lem3601830 A _39018)). Qed.
Lemma lem3601832 {A : Type'} (_39018 : type636 A) : (term238 A _39018) = (term258 A _39018).
Proof. exact (EQ_MP (@lem3601831 A _39018) (@lem3601809 A _39018)). Qed.
Lemma lem3601953 {A : Type'} (_39018 : type636 A) : (term190 A _39018) = (term258 A _39018).
Proof. exact (TRANS (@lem3601805 A _39018) (@lem3601832 A _39018)). Qed.
Lemma lem3601955 {A : Type'} (P : Prop) (Q : A -> Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3601956 {A : Type'} (P : Prop) (Q : A -> Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3601955 A P Q). Qed.
Lemma lem3601957 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term261 A _39018 GEN_PVAR_91 s P) = (term262 A _39018 GEN_PVAR_91 s P).
Proof. exact (@lem3601956 A (term263 A _39018 s P GEN_PVAR_91) (term51 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601958 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term170 A GEN_PVAR_91 s P x) = (term50 A GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term170 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601959 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term264 A GEN_PVAR_91 s P) = (term51 A GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3601958 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601960 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3601961 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term265 A GEN_PVAR_91 s P) = (term52 A GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601960 A) (@lem3601959 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601962 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term176 A _39018 s P GEN_PVAR_91) = (term176 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term176 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601963 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term261 A _39018 GEN_PVAR_91 s P) = (term177 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601962 A _39018 s P GEN_PVAR_91) (@lem3601961 A GEN_PVAR_91 s P)). Qed.
Lemma lem3601964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601965 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term266 A _39018 GEN_PVAR_91 s P) = (term267 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601964) (@lem3601963 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601966 {A : Type'} (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term170 A GEN_PVAR_91 s P x) = (term50 A GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term170 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601967 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (GEN_PVAR_91 : A) : (term176 A _39018 s P GEN_PVAR_91) = (term176 A _39018 s P GEN_PVAR_91).
Proof. exact (eq_refl (term176 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601968 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term268 A _39018 GEN_PVAR_91 s P x) = (term269 A _39018 GEN_PVAR_91 s P x).
Proof. exact (MK_COMB (@lem3601967 A _39018 s P GEN_PVAR_91) (@lem3601966 A GEN_PVAR_91 s P x)). Qed.
Lemma lem3601969 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term270 A _39018 GEN_PVAR_91 s P) = (term271 A _39018 GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3601968 A _39018 GEN_PVAR_91 s P x)). Qed.
Lemma lem3601970 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3601971 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term262 A _39018 GEN_PVAR_91 s P) = (term272 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601970 A) (@lem3601969 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601972 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : ((term261 A _39018 GEN_PVAR_91 s P) = (term262 A _39018 GEN_PVAR_91 s P)) = ((term177 A _39018 GEN_PVAR_91 s P) = (term272 A _39018 GEN_PVAR_91 s P)).
Proof. exact (MK_COMB (@lem3601965 A _39018 GEN_PVAR_91 s P) (@lem3601971 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601973 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term177 A _39018 GEN_PVAR_91 s P) = (term272 A _39018 GEN_PVAR_91 s P).
Proof. exact (EQ_MP (@lem3601972 A _39018 GEN_PVAR_91 s P) (@lem3601957 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601974 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term196 A _39018 s P) = (term273 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601973 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601976 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term211 A _39018 s P) = (term274 A _39018 s P).
Proof. exact (MK_COMB (@lem3601975 A) (@lem3601974 A _39018 s P)). Qed.
Lemma lem3601978 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3601979 {A : Type'} (P : type1402 A) : (term277 A P) = (term278 A P).
Proof. exact (@lem3601978 A A P). Qed.
Lemma lem3601980 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term279 A _39018 s P) = (term280 A _39018 s P).
Proof. exact (@lem3601979 A (term281 A _39018 s P)). Qed.
Lemma lem3601981 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term282 A _39018 s P GEN_PVAR_91) = (term271 A _39018 GEN_PVAR_91 s P).
Proof. exact (eq_refl (term282 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601982 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3601983 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term283 A _39018 s P GEN_PVAR_91 x) = (term284 A _39018 GEN_PVAR_91 s P x).
Proof. exact (MK_COMB (@lem3601981 A _39018 GEN_PVAR_91 s P) (@lem3601982 A x)). Qed.
Lemma lem3601984 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term284 A _39018 GEN_PVAR_91 s P x) = (term269 A _39018 GEN_PVAR_91 s P x).
Proof. exact (eq_refl (term284 A _39018 GEN_PVAR_91 s P x)). Qed.
Lemma lem3601985 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term283 A _39018 s P GEN_PVAR_91 x) = (term269 A _39018 GEN_PVAR_91 s P x).
Proof. exact (TRANS (@lem3601983 A _39018 GEN_PVAR_91 s P x) (@lem3601984 A _39018 GEN_PVAR_91 s P x)). Qed.
Lemma lem3601986 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term285 A _39018 s P GEN_PVAR_91) = (term271 A _39018 GEN_PVAR_91 s P).
Proof. exact (fun_ext (fun x : A => @lem3601985 A _39018 GEN_PVAR_91 s P x)). Qed.
Lemma lem3601987 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3601988 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term286 A _39018 s P GEN_PVAR_91) = (term272 A _39018 GEN_PVAR_91 s P).
Proof. exact (MK_COMB (@lem3601987 A) (@lem3601986 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601989 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term287 A _39018 s P) = (term273 A _39018 s P).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601988 A _39018 GEN_PVAR_91 s P)). Qed.
Lemma lem3601990 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3601991 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term279 A _39018 s P) = (term274 A _39018 s P).
Proof. exact (MK_COMB (@lem3601990 A) (@lem3601989 A _39018 s P)). Qed.
Lemma lem3601992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3601993 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term288 A _39018 s P) = (term289 A _39018 s P).
Proof. exact (MK_COMB (@lem3601992) (@lem3601991 A _39018 s P)). Qed.
Lemma lem3601994 {A : Type'} (_39018 : type636 A) (GEN_PVAR_91 : A) (s : A -> Prop) (P : A -> Prop) : (term282 A _39018 s P GEN_PVAR_91) = (term271 A _39018 GEN_PVAR_91 s P).
Proof. exact (eq_refl (term282 A _39018 s P GEN_PVAR_91)). Qed.
Lemma lem3601995 {A : Type'} (x : A -> A) (GEN_PVAR_91 : A) : (x GEN_PVAR_91) = (x GEN_PVAR_91).
Proof. exact (eq_refl (x GEN_PVAR_91)). Qed.
Lemma lem3601996 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) (GEN_PVAR_91 : A) : (term290 A _39018 s P x GEN_PVAR_91) = (term291 A _39018 s P x GEN_PVAR_91).
Proof. exact (MK_COMB (@lem3601994 A _39018 GEN_PVAR_91 s P) (@lem3601995 A x GEN_PVAR_91)). Qed.
Lemma lem3601997 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) (GEN_PVAR_91 : A) : (term291 A _39018 s P x GEN_PVAR_91) = (term292 A _39018 s P x GEN_PVAR_91).
Proof. exact (eq_refl (term291 A _39018 s P x GEN_PVAR_91)). Qed.
Lemma lem3601998 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) (GEN_PVAR_91 : A) : (term290 A _39018 s P x GEN_PVAR_91) = (term292 A _39018 s P x GEN_PVAR_91).
Proof. exact (TRANS (@lem3601996 A _39018 s P x GEN_PVAR_91) (@lem3601997 A _39018 s P x GEN_PVAR_91)). Qed.
Lemma lem3601999 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) : (term293 A _39018 s P x) = (term294 A _39018 s P x).
Proof. exact (fun_ext (fun GEN_PVAR_91 : A => @lem3601998 A _39018 s P x GEN_PVAR_91)). Qed.
Lemma lem3602000 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3602001 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) : (term295 A _39018 s P x) = (term296 A _39018 s P x).
Proof. exact (MK_COMB (@lem3602000 A) (@lem3601999 A _39018 s P x)). Qed.
Lemma lem3602002 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term297 A _39018 s P) = (term298 A _39018 s P).
Proof. exact (fun_ext (fun x : A -> A => @lem3602001 A _39018 s P x)). Qed.
Lemma lem3602003 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3602004 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term280 A _39018 s P) = (term299 A _39018 s P).
Proof. exact (MK_COMB (@lem3602003 A) (@lem3602002 A _39018 s P)). Qed.
Lemma lem3602005 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : ((term279 A _39018 s P) = (term280 A _39018 s P)) = ((term274 A _39018 s P) = (term299 A _39018 s P)).
Proof. exact (MK_COMB (@lem3601993 A _39018 s P) (@lem3602004 A _39018 s P)). Qed.
Lemma lem3602006 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term274 A _39018 s P) = (term299 A _39018 s P).
Proof. exact (EQ_MP (@lem3602005 A _39018 s P) (@lem3601980 A _39018 s P)). Qed.
Lemma lem3602007 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term211 A _39018 s P) = (term299 A _39018 s P).
Proof. exact (TRANS (@lem3601976 A _39018 s P) (@lem3602006 A _39018 s P)). Qed.
Lemma lem3602008 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term220 A _39018 s) = (term300 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602007 A _39018 s P)). Qed.
Lemma lem3602009 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602010 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term235 A _39018 s) = (term301 A _39018 s).
Proof. exact (MK_COMB (@lem3602009 A) (@lem3602008 A _39018 s)). Qed.
Lemma lem3602012 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3602013 {A : Type'} (P : type624 A) : (term302 A P) = (term303 A P).
Proof. exact (@lem3602012 (A -> Prop) (A -> A) P). Qed.
Lemma lem3602014 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term304 A _39018 s) = (term305 A _39018 s).
Proof. exact (@lem3602013 A (term306 A _39018 s)). Qed.
Lemma lem3602015 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term307 A _39018 s P) = (term298 A _39018 s P).
Proof. exact (eq_refl (term307 A _39018 s P)). Qed.
Lemma lem3602016 {A : Type'} (x : A -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3602017 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) : (term308 A _39018 s P x) = (term309 A _39018 s P x).
Proof. exact (MK_COMB (@lem3602015 A _39018 s P) (@lem3602016 A x)). Qed.
Lemma lem3602018 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) : (term309 A _39018 s P x) = (term296 A _39018 s P x).
Proof. exact (eq_refl (term309 A _39018 s P x)). Qed.
Lemma lem3602019 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (x : A -> A) : (term308 A _39018 s P x) = (term296 A _39018 s P x).
Proof. exact (TRANS (@lem3602017 A _39018 s P x) (@lem3602018 A _39018 s P x)). Qed.
Lemma lem3602020 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term310 A _39018 s P) = (term298 A _39018 s P).
Proof. exact (fun_ext (fun x : A -> A => @lem3602019 A _39018 s P x)). Qed.
Lemma lem3602021 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3602022 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term311 A _39018 s P) = (term299 A _39018 s P).
Proof. exact (MK_COMB (@lem3602021 A) (@lem3602020 A _39018 s P)). Qed.
Lemma lem3602023 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term312 A _39018 s) = (term300 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602022 A _39018 s P)). Qed.
Lemma lem3602024 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602025 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term304 A _39018 s) = (term301 A _39018 s).
Proof. exact (MK_COMB (@lem3602024 A) (@lem3602023 A _39018 s)). Qed.
Lemma lem3602026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3602027 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term313 A _39018 s) = (term314 A _39018 s).
Proof. exact (MK_COMB (@lem3602026) (@lem3602025 A _39018 s)). Qed.
Lemma lem3602028 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term307 A _39018 s P) = (term298 A _39018 s P).
Proof. exact (eq_refl (term307 A _39018 s P)). Qed.
Lemma lem3602029 {A : Type'} (x : type670 A) (P : A -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem3602030 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) (P : A -> Prop) : (term315 A _39018 s x P) = (term316 A _39018 s x P).
Proof. exact (MK_COMB (@lem3602028 A _39018 s P) (@lem3602029 A x P)). Qed.
Lemma lem3602031 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) (P : A -> Prop) : (term316 A _39018 s x P) = (term317 A _39018 s x P).
Proof. exact (eq_refl (term316 A _39018 s x P)). Qed.
Lemma lem3602032 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) (P : A -> Prop) : (term315 A _39018 s x P) = (term317 A _39018 s x P).
Proof. exact (TRANS (@lem3602030 A _39018 s x P) (@lem3602031 A _39018 s x P)). Qed.
Lemma lem3602033 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) : (term318 A _39018 s x) = (term319 A _39018 s x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602032 A _39018 s x P)). Qed.
Lemma lem3602034 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602035 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) : (term320 A _39018 s x) = (term321 A _39018 s x).
Proof. exact (MK_COMB (@lem3602034 A) (@lem3602033 A _39018 s x)). Qed.
Lemma lem3602036 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term322 A _39018 s) = (term323 A _39018 s).
Proof. exact (fun_ext (fun x : type670 A => @lem3602035 A _39018 s x)). Qed.
Lemma lem3602037 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem3602038 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term305 A _39018 s) = (term324 A _39018 s).
Proof. exact (MK_COMB (@lem3602037 A) (@lem3602036 A _39018 s)). Qed.
Lemma lem3602039 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((term304 A _39018 s) = (term305 A _39018 s)) = ((term301 A _39018 s) = (term324 A _39018 s)).
Proof. exact (MK_COMB (@lem3602027 A _39018 s) (@lem3602038 A _39018 s)). Qed.
Lemma lem3602040 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term301 A _39018 s) = (term324 A _39018 s).
Proof. exact (EQ_MP (@lem3602039 A _39018 s) (@lem3602014 A _39018 s)). Qed.
Lemma lem3602041 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term235 A _39018 s) = (term324 A _39018 s).
Proof. exact (TRANS (@lem3602010 A _39018 s) (@lem3602040 A _39018 s)). Qed.
Lemma lem3602042 {A : Type'} (_39018 : type636 A) : (term242 A _39018) = (term325 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602041 A _39018 s)). Qed.
Lemma lem3602043 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602044 {A : Type'} (_39018 : type636 A) : (term257 A _39018) = (term326 A _39018).
Proof. exact (MK_COMB (@lem3602043 A) (@lem3602042 A _39018)). Qed.
Lemma lem3602046 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3602047 {A : Type'} (P : type595 A) : (term327 A P) = (term328 A P).
Proof. exact (@lem3602046 (A -> Prop) (type670 A) P). Qed.
Lemma lem3602048 {A : Type'} (_39018 : type636 A) : (term329 A _39018) = (term330 A _39018).
Proof. exact (@lem3602047 A (term331 A _39018)). Qed.
Lemma lem3602049 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term332 A _39018 s) = (term323 A _39018 s).
Proof. exact (eq_refl (term332 A _39018 s)). Qed.
Lemma lem3602050 {A : Type'} (x : type670 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3602051 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) : (term333 A _39018 s x) = (term334 A _39018 s x).
Proof. exact (MK_COMB (@lem3602049 A _39018 s) (@lem3602050 A x)). Qed.
Lemma lem3602052 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) : (term334 A _39018 s x) = (term321 A _39018 s x).
Proof. exact (eq_refl (term334 A _39018 s x)). Qed.
Lemma lem3602053 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (x : type670 A) : (term333 A _39018 s x) = (term321 A _39018 s x).
Proof. exact (TRANS (@lem3602051 A _39018 s x) (@lem3602052 A _39018 s x)). Qed.
Lemma lem3602054 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term335 A _39018 s) = (term323 A _39018 s).
Proof. exact (fun_ext (fun x : type670 A => @lem3602053 A _39018 s x)). Qed.
Lemma lem3602055 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem3602056 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term336 A _39018 s) = (term324 A _39018 s).
Proof. exact (MK_COMB (@lem3602055 A) (@lem3602054 A _39018 s)). Qed.
Lemma lem3602057 {A : Type'} (_39018 : type636 A) : (term337 A _39018) = (term325 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602056 A _39018 s)). Qed.
Lemma lem3602058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602059 {A : Type'} (_39018 : type636 A) : (term329 A _39018) = (term326 A _39018).
Proof. exact (MK_COMB (@lem3602058 A) (@lem3602057 A _39018)). Qed.
Lemma lem3602060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3602061 {A : Type'} (_39018 : type636 A) : (term338 A _39018) = (term339 A _39018).
Proof. exact (MK_COMB (@lem3602060) (@lem3602059 A _39018)). Qed.
Lemma lem3602062 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term332 A _39018 s) = (term323 A _39018 s).
Proof. exact (eq_refl (term332 A _39018 s)). Qed.
Lemma lem3602063 {A : Type'} (x : type635 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3602064 {A : Type'} (_39018 : type636 A) (x : type635 A) (s : A -> Prop) : (term340 A _39018 x s) = (term341 A _39018 x s).
Proof. exact (MK_COMB (@lem3602062 A _39018 s) (@lem3602063 A x s)). Qed.
Lemma lem3602065 {A : Type'} (_39018 : type636 A) (x : type635 A) (s : A -> Prop) : (term341 A _39018 x s) = (term342 A _39018 x s).
Proof. exact (eq_refl (term341 A _39018 x s)). Qed.
Lemma lem3602066 {A : Type'} (_39018 : type636 A) (x : type635 A) (s : A -> Prop) : (term340 A _39018 x s) = (term342 A _39018 x s).
Proof. exact (TRANS (@lem3602064 A _39018 x s) (@lem3602065 A _39018 x s)). Qed.
Lemma lem3602067 {A : Type'} (_39018 : type636 A) (x : type635 A) : (term343 A _39018 x) = (term344 A _39018 x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602066 A _39018 x s)). Qed.
Lemma lem3602068 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602069 {A : Type'} (_39018 : type636 A) (x : type635 A) : (term345 A _39018 x) = (term346 A _39018 x).
Proof. exact (MK_COMB (@lem3602068 A) (@lem3602067 A _39018 x)). Qed.
Lemma lem3602070 {A : Type'} (_39018 : type636 A) : (term347 A _39018) = (term348 A _39018).
Proof. exact (fun_ext (fun x : type635 A => @lem3602069 A _39018 x)). Qed.
Lemma lem3602071 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> A))). Qed.
Lemma lem3602072 {A : Type'} (_39018 : type636 A) : (term330 A _39018) = (term349 A _39018).
Proof. exact (MK_COMB (@lem3602071 A) (@lem3602070 A _39018)). Qed.
Lemma lem3602073 {A : Type'} (_39018 : type636 A) : ((term329 A _39018) = (term330 A _39018)) = ((term326 A _39018) = (term349 A _39018)).
Proof. exact (MK_COMB (@lem3602061 A _39018) (@lem3602072 A _39018)). Qed.
Lemma lem3602074 {A : Type'} (_39018 : type636 A) : (term326 A _39018) = (term349 A _39018).
Proof. exact (EQ_MP (@lem3602073 A _39018) (@lem3602048 A _39018)). Qed.
Lemma lem3602075 {A : Type'} (_39018 : type636 A) : (term257 A _39018) = (term349 A _39018).
Proof. exact (TRANS (@lem3602044 A _39018) (@lem3602074 A _39018)). Qed.
Lemma lem3602076 {A : Type'} (_39018 : type636 A) : (term254 A _39018) = (term254 A _39018).
Proof. exact (eq_refl (term254 A _39018)). Qed.
Lemma lem3602077 {A : Type'} (_39018 : type636 A) : (term258 A _39018) = (term350 A _39018).
Proof. exact (MK_COMB (@lem3602076 A _39018) (@lem3602075 A _39018)). Qed.
Lemma lem3602079 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3602080 {A : Type'} (P : Prop) (Q : type137 A) : (term353 A P Q) = (term354 A P Q).
Proof. exact (@lem3602079 (type635 A) P Q). Qed.
Lemma lem3602081 {A : Type'} (_39018 : type636 A) : (term355 A _39018) = (term356 A _39018).
Proof. exact (@lem3602080 A (term252 A _39018) (term348 A _39018)). Qed.
Lemma lem3602082 {A : Type'} (_39018 : type636 A) (x : type635 A) : (term357 A _39018 x) = (term346 A _39018 x).
Proof. exact (eq_refl (term357 A _39018 x)). Qed.
Lemma lem3602083 {A : Type'} (_39018 : type636 A) : (term358 A _39018) = (term348 A _39018).
Proof. exact (fun_ext (fun x : type635 A => @lem3602082 A _39018 x)). Qed.
Lemma lem3602084 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> A))). Qed.
Lemma lem3602085 {A : Type'} (_39018 : type636 A) : (term359 A _39018) = (term349 A _39018).
Proof. exact (MK_COMB (@lem3602084 A) (@lem3602083 A _39018)). Qed.
Lemma lem3602086 {A : Type'} (_39018 : type636 A) : (term254 A _39018) = (term254 A _39018).
Proof. exact (eq_refl (term254 A _39018)). Qed.
Lemma lem3602087 {A : Type'} (_39018 : type636 A) : (term355 A _39018) = (term350 A _39018).
Proof. exact (MK_COMB (@lem3602086 A _39018) (@lem3602085 A _39018)). Qed.
Lemma lem3602088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3602089 {A : Type'} (_39018 : type636 A) : (term360 A _39018) = (term361 A _39018).
Proof. exact (MK_COMB (@lem3602088) (@lem3602087 A _39018)). Qed.
Lemma lem3602090 {A : Type'} (_39018 : type636 A) (x : type635 A) : (term357 A _39018 x) = (term346 A _39018 x).
Proof. exact (eq_refl (term357 A _39018 x)). Qed.
Lemma lem3602091 {A : Type'} (_39018 : type636 A) : (term254 A _39018) = (term254 A _39018).
Proof. exact (eq_refl (term254 A _39018)). Qed.
Lemma lem3602092 {A : Type'} (_39018 : type636 A) (x : type635 A) : (term362 A _39018 x) = (term363 A _39018 x).
Proof. exact (MK_COMB (@lem3602091 A _39018) (@lem3602090 A _39018 x)). Qed.
Lemma lem3602093 {A : Type'} (_39018 : type636 A) : (term364 A _39018) = (term365 A _39018).
Proof. exact (fun_ext (fun x : type635 A => @lem3602092 A _39018 x)). Qed.
Lemma lem3602094 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> A))). Qed.
Lemma lem3602095 {A : Type'} (_39018 : type636 A) : (term356 A _39018) = (term366 A _39018).
Proof. exact (MK_COMB (@lem3602094 A) (@lem3602093 A _39018)). Qed.
Lemma lem3602096 {A : Type'} (_39018 : type636 A) : ((term355 A _39018) = (term356 A _39018)) = ((term350 A _39018) = (term366 A _39018)).
Proof. exact (MK_COMB (@lem3602089 A _39018) (@lem3602095 A _39018)). Qed.
Lemma lem3602097 {A : Type'} (_39018 : type636 A) : (term350 A _39018) = (term366 A _39018).
Proof. exact (EQ_MP (@lem3602096 A _39018) (@lem3602081 A _39018)). Qed.
Lemma lem3602098 {A : Type'} (_39018 : type636 A) : (term258 A _39018) = (term366 A _39018).
Proof. exact (TRANS (@lem3602077 A _39018) (@lem3602097 A _39018)). Qed.
Lemma lem3602099 {A : Type'} (_39018 : type636 A) : (term190 A _39018) = (term366 A _39018).
Proof. exact (TRANS (@lem3601953 A _39018) (@lem3602098 A _39018)). Qed.
Lemma lem3602100 {A : Type'} (_39018 : type636 A) : (term131 A _39018) = (term366 A _39018).
Proof. exact (TRANS (@lem3601520 A _39018) (@lem3602099 A _39018)). Qed.
Lemma lem3602101 {A : Type'} (_39018 : type636 A) (h1 : term131 A _39018) : term366 A _39018.
Proof. exact (EQ_MP (@lem3602100 A _39018) (@lem3600860 A _39018 h1)). Qed.
Lemma lem3602108 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term367 A _39018 s P) = (term368 A _39018 s P).
Proof. exact (@lem17362 (@FINITE A s) (term61 A _39018 s P)). Qed.
Lemma lem3602109 {A : Type'} (P : type686 A) : (term369 A P) = (term370 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3602110 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term371 A _39018 s) = (term372 A _39018 s).
Proof. exact (@lem3602109 A (term66 A _39018 s)). Qed.
Lemma lem3602111 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term373 A _39018 s P) = (term64 A _39018 s P).
Proof. exact (eq_refl (term373 A _39018 s P)). Qed.
Lemma lem3602112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3602113 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term374 A _39018 s P) = (term367 A _39018 s P).
Proof. exact (MK_COMB (@lem3602112) (@lem3602111 A _39018 s P)). Qed.
Lemma lem3602114 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term374 A _39018 s P) = (term368 A _39018 s P).
Proof. exact (TRANS (@lem3602113 A _39018 s P) (@lem3602108 A _39018 s P)). Qed.
Lemma lem3602115 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term375 A _39018 s) = (term376 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602114 A _39018 s P)). Qed.
Lemma lem3602116 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602117 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term372 A _39018 s) = (term377 A _39018 s).
Proof. exact (MK_COMB (@lem3602116 A) (@lem3602115 A _39018 s)). Qed.
Lemma lem3602118 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term371 A _39018 s) = (term377 A _39018 s).
Proof. exact (TRANS (@lem3602110 A _39018 s) (@lem3602117 A _39018 s)). Qed.
Lemma lem3602119 {A : Type'} (P : type686 A) : (term369 A P) = (term370 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3602120 {A : Type'} (_39018 : type636 A) : (term72 A _39018) = (term378 A _39018).
Proof. exact (@lem3602119 A (term70 A _39018)). Qed.
Lemma lem3602121 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term379 A _39018 s) = (term68 A _39018 s).
Proof. exact (eq_refl (term379 A _39018 s)). Qed.
Lemma lem3602122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3602123 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term380 A _39018 s) = (term371 A _39018 s).
Proof. exact (MK_COMB (@lem3602122) (@lem3602121 A _39018 s)). Qed.
Lemma lem3602124 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term380 A _39018 s) = (term377 A _39018 s).
Proof. exact (TRANS (@lem3602123 A _39018 s) (@lem3602118 A _39018 s)). Qed.
Lemma lem3602125 {A : Type'} (_39018 : type636 A) : (term381 A _39018) = (term382 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602124 A _39018 s)). Qed.
Lemma lem3602126 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602127 {A : Type'} (_39018 : type636 A) : (term378 A _39018) = (term383 A _39018).
Proof. exact (MK_COMB (@lem3602126 A) (@lem3602125 A _39018)). Qed.
Lemma lem3602128 {A : Type'} (_39018 : type636 A) : (term72 A _39018) = (term383 A _39018).
Proof. exact (TRANS (@lem3602120 A _39018) (@lem3602127 A _39018)). Qed.
Lemma lem3602134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term352 A P Q) = (term351 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem3602135 {A : Type'} (P : Prop) (Q : type686 A) : (term384 A P Q) = (term385 A P Q).
Proof. exact (@lem3602134 (A -> Prop) P Q). Qed.
Lemma lem3602136 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term386 A _39018 s) = (term387 A _39018 s).
Proof. exact (@lem3602135 A (@FINITE A s) (term388 A _39018 s)). Qed.
Lemma lem3602137 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term389 A _39018 s P) = (term390 A _39018 s P).
Proof. exact (eq_refl (term389 A _39018 s P)). Qed.
Lemma lem3602138 {A : Type'} (s : A -> Prop) : (term391 A s) = (term391 A s).
Proof. exact (eq_refl (term391 A s)). Qed.
Lemma lem3602139 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term392 A _39018 s P) = (term368 A _39018 s P).
Proof. exact (MK_COMB (@lem3602138 A s) (@lem3602137 A _39018 s P)). Qed.
Lemma lem3602140 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term393 A _39018 s) = (term376 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602139 A _39018 s P)). Qed.
Lemma lem3602141 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602142 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term386 A _39018 s) = (term377 A _39018 s).
Proof. exact (MK_COMB (@lem3602141 A) (@lem3602140 A _39018 s)). Qed.
Lemma lem3602143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3602144 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term394 A _39018 s) = (term395 A _39018 s).
Proof. exact (MK_COMB (@lem3602143) (@lem3602142 A _39018 s)). Qed.
Lemma lem3602145 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term389 A _39018 s P) = (term390 A _39018 s P).
Proof. exact (eq_refl (term389 A _39018 s P)). Qed.
Lemma lem3602146 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term396 A _39018 s) = (term388 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602145 A _39018 s P)). Qed.
Lemma lem3602147 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602148 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term397 A _39018 s) = (term398 A _39018 s).
Proof. exact (MK_COMB (@lem3602147 A) (@lem3602146 A _39018 s)). Qed.
Lemma lem3602149 {A : Type'} (s : A -> Prop) : (term391 A s) = (term391 A s).
Proof. exact (eq_refl (term391 A s)). Qed.
Lemma lem3602150 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term387 A _39018 s) = (term399 A _39018 s).
Proof. exact (MK_COMB (@lem3602149 A s) (@lem3602148 A _39018 s)). Qed.
Lemma lem3602151 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((term386 A _39018 s) = (term387 A _39018 s)) = ((term377 A _39018 s) = (term399 A _39018 s)).
Proof. exact (MK_COMB (@lem3602144 A _39018 s) (@lem3602150 A _39018 s)). Qed.
Lemma lem3602152 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term377 A _39018 s) = (term399 A _39018 s).
Proof. exact (EQ_MP (@lem3602151 A _39018 s) (@lem3602136 A _39018 s)). Qed.
Lemma lem3602157 {A : Type'} (_39018 : type636 A) : (term382 A _39018) = (term400 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602152 A _39018 s)). Qed.
Lemma lem3602158 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602159 {A : Type'} (_39018 : type636 A) : (term383 A _39018) = (term401 A _39018).
Proof. exact (MK_COMB (@lem3602158 A) (@lem3602157 A _39018)). Qed.
Lemma lem3602189 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3602190 {A : Type'} (P : Prop) (Q : type686 A) : (term385 A P Q) = (term384 A P Q).
Proof. exact (@lem3602189 (A -> Prop) P Q). Qed.
Lemma lem3602191 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term387 A _39018 s) = (term386 A _39018 s).
Proof. exact (@lem3602190 A (@FINITE A s) (term388 A _39018 s)). Qed.
Lemma lem3602192 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term389 A _39018 s P) = (term390 A _39018 s P).
Proof. exact (eq_refl (term389 A _39018 s P)). Qed.
Lemma lem3602193 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term396 A _39018 s) = (term388 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602192 A _39018 s P)). Qed.
Lemma lem3602194 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602195 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term397 A _39018 s) = (term398 A _39018 s).
Proof. exact (MK_COMB (@lem3602194 A) (@lem3602193 A _39018 s)). Qed.
Lemma lem3602196 {A : Type'} (s : A -> Prop) : (term391 A s) = (term391 A s).
Proof. exact (eq_refl (term391 A s)). Qed.
Lemma lem3602197 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term387 A _39018 s) = (term399 A _39018 s).
Proof. exact (MK_COMB (@lem3602196 A s) (@lem3602195 A _39018 s)). Qed.
Lemma lem3602198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3602199 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term402 A _39018 s) = (term403 A _39018 s).
Proof. exact (MK_COMB (@lem3602198) (@lem3602197 A _39018 s)). Qed.
Lemma lem3602200 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term389 A _39018 s P) = (term390 A _39018 s P).
Proof. exact (eq_refl (term389 A _39018 s P)). Qed.
Lemma lem3602201 {A : Type'} (s : A -> Prop) : (term391 A s) = (term391 A s).
Proof. exact (eq_refl (term391 A s)). Qed.
Lemma lem3602202 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term392 A _39018 s P) = (term368 A _39018 s P).
Proof. exact (MK_COMB (@lem3602201 A s) (@lem3602200 A _39018 s P)). Qed.
Lemma lem3602203 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term393 A _39018 s) = (term376 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602202 A _39018 s P)). Qed.
Lemma lem3602204 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602205 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term386 A _39018 s) = (term377 A _39018 s).
Proof. exact (MK_COMB (@lem3602204 A) (@lem3602203 A _39018 s)). Qed.
Lemma lem3602206 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : ((term387 A _39018 s) = (term386 A _39018 s)) = ((term399 A _39018 s) = (term377 A _39018 s)).
Proof. exact (MK_COMB (@lem3602199 A _39018 s) (@lem3602205 A _39018 s)). Qed.
Lemma lem3602207 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term399 A _39018 s) = (term377 A _39018 s).
Proof. exact (EQ_MP (@lem3602206 A _39018 s) (@lem3602191 A _39018 s)). Qed.
Lemma lem3602208 {A : Type'} (_39018 : type636 A) : (term400 A _39018) = (term382 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602207 A _39018 s)). Qed.
Lemma lem3602209 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3602210 {A : Type'} (_39018 : type636 A) : (term401 A _39018) = (term383 A _39018).
Proof. exact (MK_COMB (@lem3602209 A) (@lem3602208 A _39018)). Qed.
Lemma lem3602211 {A : Type'} (_39018 : type636 A) : (term383 A _39018) = (term383 A _39018).
Proof. exact (TRANS (@lem3602159 A _39018) (@lem3602210 A _39018)). Qed.
Lemma lem3602212 {A : Type'} (_39018 : type636 A) : (term72 A _39018) = (term383 A _39018).
Proof. exact (TRANS (@lem3602128 A _39018) (@lem3602211 A _39018)). Qed.
Lemma lem3602213 {A : Type'} (_39018 : type636 A) (h1 : term72 A _39018) : term383 A _39018.
Proof. exact (EQ_MP (@lem3602212 A _39018) (@lem3600861 A _39018 h1)). Qed.
Lemma lem3602374 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term404 A s t) = (term405 A s t).
Proof. exact (@lem17045 (@FINITE A t) (@SUBSET A s t)). Qed.
Lemma lem3602375 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3602376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3602377 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term406 A s t) = (term407 A s t).
Proof. exact (MK_COMB (@lem3602376) (@lem3602374 A s t)). Qed.
Lemma lem3602378 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term408 A t s) = (term409 A t s).
Proof. exact (MK_COMB (@lem3602377 A s t) (@lem3602375 A s)). Qed.
Lemma lem3602379 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term408 A t s).
Proof. exact (@lem17265 (term410 A s t) (@FINITE A s)). Qed.
Lemma lem3602380 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term409 A t s).
Proof. exact (TRANS (@lem3602379 A t s) (@lem3602378 A t s)). Qed.
Lemma lem3602381 {A : Type'} (s : A -> Prop) : (term55 A s) = (term411 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3602380 A t s)). Qed.
Lemma lem3602382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602383 {A : Type'} (s : A -> Prop) : (term56 A s) = (term412 A s).
Proof. exact (MK_COMB (@lem3602382 A) (@lem3602381 A s)). Qed.
Lemma lem3602384 {A : Type'} : (term57 A) = (term413 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602383 A s)). Qed.
Lemma lem3602385 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602386 {A : Type'} : (term12 A) = (term414 A).
Proof. exact (MK_COMB (@lem3602385 A) (@lem3602384 A)). Qed.
Lemma lem3602412 {A : Type'} (P : A -> Prop) (Q : Prop) : (term415 A P Q) = (term416 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3602413 {A : Type'} (P : type686 A) (Q : Prop) : (term417 A P Q) = (term418 A P Q).
Proof. exact (@lem3602412 (A -> Prop) P Q). Qed.
Lemma lem3602414 {A : Type'} (s : A -> Prop) : (term419 A s) = (term420 A s).
Proof. exact (@lem3602413 A (term421 A s) (@FINITE A s)). Qed.
Lemma lem3602415 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term422 A s t) = (term405 A s t).
Proof. exact (eq_refl (term422 A s t)). Qed.
Lemma lem3602416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3602417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term423 A s t) = (term407 A s t).
Proof. exact (MK_COMB (@lem3602416) (@lem3602415 A s t)). Qed.
Lemma lem3602418 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3602419 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term424 A t s) = (term409 A t s).
Proof. exact (MK_COMB (@lem3602417 A s t) (@lem3602418 A s)). Qed.
Lemma lem3602420 {A : Type'} (s : A -> Prop) : (term425 A s) = (term411 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3602419 A t s)). Qed.
Lemma lem3602421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602422 {A : Type'} (s : A -> Prop) : (term419 A s) = (term412 A s).
Proof. exact (MK_COMB (@lem3602421 A) (@lem3602420 A s)). Qed.
Lemma lem3602423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3602424 {A : Type'} (s : A -> Prop) : (term426 A s) = (term427 A s).
Proof. exact (MK_COMB (@lem3602423) (@lem3602422 A s)). Qed.
Lemma lem3602425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term422 A s t) = (term405 A s t).
Proof. exact (eq_refl (term422 A s t)). Qed.
Lemma lem3602426 {A : Type'} (s : A -> Prop) : (term428 A s) = (term421 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3602425 A s t)). Qed.
Lemma lem3602427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602428 {A : Type'} (s : A -> Prop) : (term429 A s) = (term430 A s).
Proof. exact (MK_COMB (@lem3602427 A) (@lem3602426 A s)). Qed.
Lemma lem3602429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3602430 {A : Type'} (s : A -> Prop) : (term431 A s) = (term432 A s).
Proof. exact (MK_COMB (@lem3602429) (@lem3602428 A s)). Qed.
Lemma lem3602431 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3602432 {A : Type'} (s : A -> Prop) : (term420 A s) = (term433 A s).
Proof. exact (MK_COMB (@lem3602430 A s) (@lem3602431 A s)). Qed.
Lemma lem3602433 {A : Type'} (s : A -> Prop) : ((term419 A s) = (term420 A s)) = ((term412 A s) = (term433 A s)).
Proof. exact (MK_COMB (@lem3602424 A s) (@lem3602432 A s)). Qed.
Lemma lem3602434 {A : Type'} (s : A -> Prop) : (term412 A s) = (term433 A s).
Proof. exact (EQ_MP (@lem3602433 A s) (@lem3602414 A s)). Qed.
Lemma lem3602483 {A : Type'} : (term413 A) = (term434 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602434 A s)). Qed.
Lemma lem3602484 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602519 {A : Type'} : (term414 A) = (term435 A).
Proof. exact (MK_COMB (@lem3602484 A) (@lem3602483 A)). Qed.
Lemma lem3602520 {A : Type'} : (term12 A) = (term435 A).
Proof. exact (TRANS (@lem3602386 A) (@lem3602519 A)). Qed.
Lemma lem3602521 {A : Type'} (h1 : term12 A) : term435 A.
Proof. exact (EQ_MP (@lem3602520 A) (@lem3600863 A h1)). Qed.
Lemma lem3602542 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term41 A _39018 P s) = (term41 A _39018 P s).
Proof. exact (eq_refl (term41 A _39018 P s)). Qed.
Lemma lem3602543 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term43 A _39018 s) = (term43 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602542 A _39018 P s)). Qed.
Lemma lem3602544 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602545 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term45 A _39018 s) = (term45 A _39018 s).
Proof. exact (MK_COMB (@lem3602544 A) (@lem3602543 A _39018 s)). Qed.
Lemma lem3602546 {A : Type'} (_39018 : type636 A) : (term47 A _39018) = (term47 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602545 A _39018 s)). Qed.
Lemma lem3602547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602560 {A : Type'} (_39018 : type636 A) : (term48 A _39018) = (term48 A _39018).
Proof. exact (MK_COMB (@lem3602547 A) (@lem3602546 A _39018)). Qed.
Lemma lem3602561 {A : Type'} (_39018 : type636 A) (h1 : term48 A _39018) : term48 A _39018.
Proof. exact (EQ_MP (@lem3602560 A _39018) (@lem3600865 A _39018 h1)). Qed.
Lemma lem3602562 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (h1 : term377 A _39018 s) : term377 A _39018 s.
Proof. exact (h1). Qed.
Lemma lem3602563 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : term368 A _39018 s P.
Proof. exact (h1). Qed.
Lemma lem3602620 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602621 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3602620 (A -> Prop) Prop f x). Qed.
Lemma lem3602623 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3602621 A (@FINITE A) s). Qed.
Lemma lem3602624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3602631 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602632 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3602631 (A -> Prop) (type686 A) f x). Qed.
Lemma lem3602633 {A : Type'} (s : A -> Prop) : (@SUBSET A s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) s).
Proof. exact (@lem3602632 A (@SUBSET A) s). Qed.
Lemma lem3602634 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3602635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) s t).
Proof. exact (MK_COMB (@lem3602633 A s) (@lem3602634 A t)). Qed.
Lemma lem3602637 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602638 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3602637 (A -> Prop) Prop f x). Qed.
Lemma lem3602639 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) s t) = (term436 A s t).
Proof. exact (@lem3602638 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) s) t). Qed.
Lemma lem3602641 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term436 A s t).
Proof. exact (TRANS (@lem3602635 A s t) (@lem3602639 A s t)). Qed.
Lemma lem3602642 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term437 A s t) = (term438 A s t).
Proof. exact (MK_COMB (@lem3602624) (@lem3602641 A s t)). Qed.
Lemma lem3602643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3602648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602649 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3602648 (A -> Prop) Prop f x). Qed.
Lemma lem3602651 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@I ((A -> Prop) -> Prop) (@FINITE A) t).
Proof. exact (@lem3602649 A (@FINITE A) t). Qed.
Lemma lem3602652 {A : Type'} (t : A -> Prop) : (term439 A t) = (term440 A t).
Proof. exact (MK_COMB (@lem3602643) (@lem3602651 A t)). Qed.
Lemma lem3602653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3602654 {A : Type'} (t : A -> Prop) : (term441 A t) = (term442 A t).
Proof. exact (MK_COMB (@lem3602653) (@lem3602652 A t)). Qed.
Lemma lem3602655 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term405 A s t) = (term443 A s t).
Proof. exact (MK_COMB (@lem3602654 A t) (@lem3602642 A s t)). Qed.
Lemma lem3602656 {A : Type'} (s : A -> Prop) : (term421 A s) = (term444 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3602655 A s t)). Qed.
Lemma lem3602657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602658 {A : Type'} (s : A -> Prop) : (term430 A s) = (term445 A s).
Proof. exact (MK_COMB (@lem3602657 A) (@lem3602656 A s)). Qed.
Lemma lem3602659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3602660 {A : Type'} (s : A -> Prop) : (term432 A s) = (term446 A s).
Proof. exact (MK_COMB (@lem3602659) (@lem3602658 A s)). Qed.
Lemma lem3602661 {A : Type'} (s : A -> Prop) : (term433 A s) = (term447 A s).
Proof. exact (MK_COMB (@lem3602660 A s) (@lem3602623 A s)). Qed.
Lemma lem3602662 {A : Type'} : (term434 A) = (term448 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602661 A s)). Qed.
Lemma lem3602663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602664 {A : Type'} : (term435 A) = (term449 A).
Proof. exact (MK_COMB (@lem3602663 A) (@lem3602662 A)). Qed.
Lemma lem3602665 {A : Type'} (h1 : term12 A) : term449 A.
Proof. exact (EQ_MP (@lem3602664 A) (@lem3602521 A h1)). Qed.
Lemma lem3602713 {A : Type'} : (@SUBSET A) = (@SUBSET A).
Proof. exact (eq_refl (@SUBSET A)). Qed.
Lemma lem3602714 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3602721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602722 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3602721 (A -> Prop) (type672 A) f x). Qed.
Lemma lem3602723 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (_39018 s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s).
Proof. exact (@lem3602722 A _39018 s). Qed.
Lemma lem3602724 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3602725 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (_39018 s P) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s P).
Proof. exact (MK_COMB (@lem3602723 A _39018 s) (@lem3602724 A P)). Qed.
Lemma lem3602727 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602728 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3602727 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3602729 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s P) = (term450 A _39018 s P).
Proof. exact (@lem3602728 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s) P). Qed.
Lemma lem3602731 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (_39018 s P) = (term450 A _39018 s P).
Proof. exact (TRANS (@lem3602725 A _39018 s P) (@lem3602729 A _39018 s P)). Qed.
Lemma lem3602732 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term37 A _39018 s P) = (term451 A _39018 s P).
Proof. exact (MK_COMB (@lem3602714 A) (@lem3602731 A _39018 s P)). Qed.
Lemma lem3602734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602735 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3602734 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3602736 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term451 A _39018 s P) = (term452 A _39018 s P).
Proof. exact (@lem3602735 A (@GSPEC A) (term450 A _39018 s P)). Qed.
Lemma lem3602737 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term37 A _39018 s P) = (term452 A _39018 s P).
Proof. exact (TRANS (@lem3602732 A _39018 s P) (@lem3602736 A _39018 s P)). Qed.
Lemma lem3602738 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3602739 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term39 A _39018 s P) = (term453 A _39018 s P).
Proof. exact (MK_COMB (@lem3602713 A) (@lem3602737 A _39018 s P)). Qed.
Lemma lem3602740 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term41 A _39018 P s) = (term454 A _39018 P s).
Proof. exact (MK_COMB (@lem3602739 A _39018 s P) (@lem3602738 A s)). Qed.
Lemma lem3602742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602743 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3602742 (A -> Prop) (type686 A) f x). Qed.
Lemma lem3602744 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term453 A _39018 s P) = (term455 A _39018 s P).
Proof. exact (@lem3602743 A (@SUBSET A) (term452 A _39018 s P)). Qed.
Lemma lem3602745 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3602746 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term454 A _39018 P s) = (term456 A _39018 P s).
Proof. exact (MK_COMB (@lem3602744 A _39018 s P) (@lem3602745 A s)). Qed.
Lemma lem3602748 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602749 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3602748 (A -> Prop) Prop f x). Qed.
Lemma lem3602750 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term456 A _39018 P s) = (term457 A _39018 P s).
Proof. exact (@lem3602749 A (term455 A _39018 s P) s). Qed.
Lemma lem3602751 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term454 A _39018 P s) = (term457 A _39018 P s).
Proof. exact (TRANS (@lem3602746 A _39018 P s) (@lem3602750 A _39018 P s)). Qed.
Lemma lem3602752 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term41 A _39018 P s) = (term457 A _39018 P s).
Proof. exact (TRANS (@lem3602740 A _39018 P s) (@lem3602751 A _39018 P s)). Qed.
Lemma lem3602753 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term43 A _39018 s) = (term458 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3602752 A _39018 P s)). Qed.
Lemma lem3602754 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602755 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term45 A _39018 s) = (term459 A _39018 s).
Proof. exact (MK_COMB (@lem3602754 A) (@lem3602753 A _39018 s)). Qed.
Lemma lem3602756 {A : Type'} (_39018 : type636 A) : (term47 A _39018) = (term460 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3602755 A _39018 s)). Qed.
Lemma lem3602757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3602758 {A : Type'} (_39018 : type636 A) : (term48 A _39018) = (term461 A _39018).
Proof. exact (MK_COMB (@lem3602757 A) (@lem3602756 A _39018)). Qed.
Lemma lem3602759 {A : Type'} (_39018 : type636 A) (h1 : term48 A _39018) : term461 A _39018.
Proof. exact (EQ_MP (@lem3602758 A _39018) (@lem3602561 A _39018 h1)). Qed.
Lemma lem3602760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3602761 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3602762 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3602769 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602770 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3602769 (A -> Prop) (type672 A) f x). Qed.
Lemma lem3602771 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (_39018 s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s).
Proof. exact (@lem3602770 A _39018 s). Qed.
Lemma lem3602772 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3602773 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (_39018 s P) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s P).
Proof. exact (MK_COMB (@lem3602771 A _39018 s) (@lem3602772 A P)). Qed.
Lemma lem3602775 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602776 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3602775 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3602777 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s P) = (term450 A _39018 s P).
Proof. exact (@lem3602776 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) _39018 s) P). Qed.
Lemma lem3602779 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (_39018 s P) = (term450 A _39018 s P).
Proof. exact (TRANS (@lem3602773 A _39018 s P) (@lem3602777 A _39018 s P)). Qed.
Lemma lem3602780 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term37 A _39018 s P) = (term451 A _39018 s P).
Proof. exact (MK_COMB (@lem3602762 A) (@lem3602779 A _39018 s P)). Qed.
Lemma lem3602782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602783 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3602782 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3602784 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term451 A _39018 s P) = (term452 A _39018 s P).
Proof. exact (@lem3602783 A (@GSPEC A) (term450 A _39018 s P)). Qed.
Lemma lem3602785 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term37 A _39018 s P) = (term452 A _39018 s P).
Proof. exact (TRANS (@lem3602780 A _39018 s P) (@lem3602784 A _39018 s P)). Qed.
Lemma lem3602786 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term61 A _39018 s P) = (term462 A _39018 s P).
Proof. exact (MK_COMB (@lem3602761 A) (@lem3602785 A _39018 s P)). Qed.
Lemma lem3602788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602789 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3602788 (A -> Prop) Prop f x). Qed.
Lemma lem3602790 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term462 A _39018 s P) = (term463 A _39018 s P).
Proof. exact (@lem3602789 A (@FINITE A) (term452 A _39018 s P)). Qed.
Lemma lem3602791 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term61 A _39018 s P) = (term463 A _39018 s P).
Proof. exact (TRANS (@lem3602786 A _39018 s P) (@lem3602790 A _39018 s P)). Qed.
Lemma lem3602792 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term390 A _39018 s P) = (term464 A _39018 s P).
Proof. exact (MK_COMB (@lem3602760) (@lem3602791 A _39018 s P)). Qed.
Lemma lem3602797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3602798 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3602797 (A -> Prop) Prop f x). Qed.
Lemma lem3602800 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3602798 A (@FINITE A) s). Qed.
Lemma lem3602801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3602802 {A : Type'} (s : A -> Prop) : (term391 A s) = (term465 A s).
Proof. exact (MK_COMB (@lem3602801) (@lem3602800 A s)). Qed.
Lemma lem3602803 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term368 A _39018 s P) = (term466 A _39018 s P).
Proof. exact (MK_COMB (@lem3602802 A s) (@lem3602792 A _39018 s P)). Qed.
Lemma lem3602804 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : term466 A _39018 s P.
Proof. exact (EQ_MP (@lem3602803 A _39018 s P) (@lem3602563 A _39018 s P h1)). Qed.
Lemma lem3603396 {A : Type'} (P : A -> Prop) (Q : Prop) : (term416 A P Q) = (term415 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3603397 {A : Type'} (P : type686 A) (Q : Prop) : (term418 A P Q) = (term417 A P Q).
Proof. exact (@lem3603396 (A -> Prop) P Q). Qed.
Lemma lem3603398 {A : Type'} (s : A -> Prop) : (term467 A s) = (term468 A s).
Proof. exact (@lem3603397 A (term444 A s) (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem3603399 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term469 A s t) = (term443 A s t).
Proof. exact (eq_refl (term469 A s t)). Qed.
Lemma lem3603400 {A : Type'} (s : A -> Prop) : (term470 A s) = (term444 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3603399 A s t)). Qed.
Lemma lem3603401 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603402 {A : Type'} (s : A -> Prop) : (term471 A s) = (term445 A s).
Proof. exact (MK_COMB (@lem3603401 A) (@lem3603400 A s)). Qed.
Lemma lem3603403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3603404 {A : Type'} (s : A -> Prop) : (term472 A s) = (term446 A s).
Proof. exact (MK_COMB (@lem3603403) (@lem3603402 A s)). Qed.
Lemma lem3603405 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> Prop) (@FINITE A) s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem3603406 {A : Type'} (s : A -> Prop) : (term467 A s) = (term447 A s).
Proof. exact (MK_COMB (@lem3603404 A s) (@lem3603405 A s)). Qed.
Lemma lem3603407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3603408 {A : Type'} (s : A -> Prop) : (term473 A s) = (term474 A s).
Proof. exact (MK_COMB (@lem3603407) (@lem3603406 A s)). Qed.
Lemma lem3603409 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term469 A s t) = (term443 A s t).
Proof. exact (eq_refl (term469 A s t)). Qed.
Lemma lem3603410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3603411 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term475 A s t) = (term476 A s t).
Proof. exact (MK_COMB (@lem3603410) (@lem3603409 A s t)). Qed.
Lemma lem3603412 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> Prop) (@FINITE A) s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem3603413 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term477 A t s) = (term478 A t s).
Proof. exact (MK_COMB (@lem3603411 A s t) (@lem3603412 A s)). Qed.
Lemma lem3603414 {A : Type'} (s : A -> Prop) : (term479 A s) = (term480 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3603413 A t s)). Qed.
Lemma lem3603415 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603416 {A : Type'} (s : A -> Prop) : (term468 A s) = (term481 A s).
Proof. exact (MK_COMB (@lem3603415 A) (@lem3603414 A s)). Qed.
Lemma lem3603417 {A : Type'} (s : A -> Prop) : ((term467 A s) = (term468 A s)) = ((term447 A s) = (term481 A s)).
Proof. exact (MK_COMB (@lem3603408 A s) (@lem3603416 A s)). Qed.
Lemma lem3603418 {A : Type'} (s : A -> Prop) : (term447 A s) = (term481 A s).
Proof. exact (EQ_MP (@lem3603417 A s) (@lem3603398 A s)). Qed.
Lemma lem3603419 {A : Type'} : (term448 A) = (term482 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3603418 A s)). Qed.
Lemma lem3603420 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603421 {A : Type'} : (term449 A) = (term483 A).
Proof. exact (MK_COMB (@lem3603420 A) (@lem3603419 A)). Qed.
Lemma lem3603434 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term478 A t s) = (term478 A t s).
Proof. exact (eq_refl (term478 A t s)). Qed.
Lemma lem3603435 {A : Type'} (s : A -> Prop) : (term480 A s) = (term480 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3603434 A t s)). Qed.
Lemma lem3603436 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603437 {A : Type'} (s : A -> Prop) : (term481 A s) = (term481 A s).
Proof. exact (MK_COMB (@lem3603436 A) (@lem3603435 A s)). Qed.
Lemma lem3603438 {A : Type'} : (term482 A) = (term482 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3603437 A s)). Qed.
Lemma lem3603439 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603440 {A : Type'} : (term483 A) = (term483 A).
Proof. exact (MK_COMB (@lem3603439 A) (@lem3603438 A)). Qed.
Lemma lem3603441 {A : Type'} : (term449 A) = (term483 A).
Proof. exact (TRANS (@lem3603421 A) (@lem3603440 A)). Qed.
Lemma lem3603442 {A : Type'} (h1 : term12 A) : term483 A.
Proof. exact (EQ_MP (@lem3603441 A) (@lem3602665 A h1)). Qed.
Lemma lem3603454 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term457 A _39018 P s) = (term457 A _39018 P s).
Proof. exact (eq_refl (term457 A _39018 P s)). Qed.
Lemma lem3603455 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term458 A _39018 s) = (term458 A _39018 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3603454 A _39018 P s)). Qed.
Lemma lem3603456 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603457 {A : Type'} (_39018 : type636 A) (s : A -> Prop) : (term459 A _39018 s) = (term459 A _39018 s).
Proof. exact (MK_COMB (@lem3603456 A) (@lem3603455 A _39018 s)). Qed.
Lemma lem3603458 {A : Type'} (_39018 : type636 A) : (term460 A _39018) = (term460 A _39018).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3603457 A _39018 s)). Qed.
Lemma lem3603459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603461 {A : Type'} (_39018 : type636 A) : (term461 A _39018) = (term461 A _39018).
Proof. exact (MK_COMB (@lem3603459 A) (@lem3603458 A _39018)). Qed.
Lemma lem3603462 {A : Type'} (_39018 : type636 A) (h1 : term48 A _39018) : term461 A _39018.
Proof. exact (EQ_MP (@lem3603461 A _39018) (@lem3602759 A _39018 h1)). Qed.
Lemma lem3603615 {A : Type'} (_39022 : A -> Prop) (h1 : term12 A) : term484 A _39022.
Proof. exact (@lem3603442 A h1 _39022). Qed.
Lemma lem3603616 {A : Type'} (_39022 : A -> Prop) : (term484 A _39022) = (term481 A _39022).
Proof. exact (eq_refl (term484 A _39022)). Qed.
Lemma lem3603617 {A : Type'} (_39022 : A -> Prop) (h1 : term12 A) : term481 A _39022.
Proof. exact (EQ_MP (@lem3603616 A _39022) (@lem3603615 A _39022 h1)). Qed.
Lemma lem3603618 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) (h1 : term12 A) : term485 A _39022 _39023.
Proof. exact (@lem3603617 A _39022 h1 _39023). Qed.
Lemma lem3603619 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) : (term485 A _39022 _39023) = (term478 A _39023 _39022).
Proof. exact (eq_refl (term485 A _39022 _39023)). Qed.
Lemma lem3603620 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) (h1 : term12 A) : term478 A _39023 _39022.
Proof. exact (EQ_MP (@lem3603619 A _39023 _39022) (@lem3603618 A _39022 _39023 h1)). Qed.
Lemma lem3603627 {A : Type'} (_39026 : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term486 A _39018 _39026.
Proof. exact (@lem3603462 A _39018 h1 _39026). Qed.
Lemma lem3603628 {A : Type'} (_39018 : type636 A) (_39026 : A -> Prop) : (term486 A _39018 _39026) = (term459 A _39018 _39026).
Proof. exact (eq_refl (term486 A _39018 _39026)). Qed.
Lemma lem3603629 {A : Type'} (_39026 : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term459 A _39018 _39026.
Proof. exact (EQ_MP (@lem3603628 A _39018 _39026) (@lem3603627 A _39026 _39018 h1)). Qed.
Lemma lem3603630 {A : Type'} (_39026 : A -> Prop) (_39027 : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term487 A _39018 _39026 _39027.
Proof. exact (@lem3603629 A _39026 _39018 h1 _39027). Qed.
Lemma lem3603631 {A : Type'} (_39018 : type636 A) (_39027 : A -> Prop) (_39026 : A -> Prop) : (term487 A _39018 _39026 _39027) = (term457 A _39018 _39027 _39026).
Proof. exact (eq_refl (term487 A _39018 _39026 _39027)). Qed.
Lemma lem3603697 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) : (term478 A _39023 _39022) = (term488 A _39023 _39022).
Proof. exact (@lem3599934 (term440 A _39023) (term438 A _39022 _39023) (@I ((A -> Prop) -> Prop) (@FINITE A) _39022)). Qed.
Lemma lem3603698 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) (h1 : term12 A) : term488 A _39023 _39022.
Proof. exact (EQ_MP (@lem3603697 A _39023 _39022) (@lem3603620 A _39023 _39022 h1)). Qed.
Lemma lem3603730 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : term464 A _39018 s P.
Proof. exact (proj2 (@lem3602804 A _39018 s P h1)). Qed.
Lemma lem3603732 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem3602804 A _39018 s P h1)). Qed.
Lemma lem3603733 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : term489 A s.
Proof. exact (fun h0 : term440 A s => @lem3603732 A _39018 s P h1). Qed.
Lemma lem3603735 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3603736 {A : Type'} (s : A -> Prop) : (term489 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3603735 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem3603737 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem3603736 A s) (@lem3603733 A _39018 s P h1)). Qed.
Lemma lem3603739 {A : Type'} (_39027 : A -> Prop) (_39026 : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term457 A _39018 _39027 _39026.
Proof. exact (EQ_MP (@lem3603631 A _39018 _39027 _39026) (@lem3603630 A _39026 _39027 _39018 h1)). Qed.
Lemma lem3603740 {A : Type'} (_39027 : A -> Prop) (_39026 : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term457 A _39018 _39027 _39026.
Proof. exact (@lem3603739 A _39027 _39026 _39018 h1). Qed.
Lemma lem3603741 {A : Type'} (P : A -> Prop) (s : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term457 A _39018 P s.
Proof. exact (@lem3603740 A P s _39018 h1). Qed.
Lemma lem3603742 {A : Type'} (P : A -> Prop) (s : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term491 A _39018 P s.
Proof. exact (fun h0 : term492 A _39018 P s => @lem3603741 A P s _39018 h1). Qed.
Lemma lem3603744 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3603745 {A : Type'} (_39018 : type636 A) (P : A -> Prop) (s : A -> Prop) : (term491 A _39018 P s) = (term457 A _39018 P s).
Proof. exact (@lem3603744 (term457 A _39018 P s)). Qed.
Lemma lem3603746 {A : Type'} (P : A -> Prop) (s : A -> Prop) (_39018 : type636 A) (h1 : term48 A _39018) : term457 A _39018 P s.
Proof. exact (EQ_MP (@lem3603745 A _39018 P s) (@lem3603742 A P s _39018 h1)). Qed.
Lemma lem3603762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3603763 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term493 A _39023 _39022) = (term494 A _39022 _39023).
Proof. exact (@lem3603762 (@I ((A -> Prop) -> Prop) (@FINITE A) _39022) (term438 A _39022 _39023)). Qed.
Lemma lem3603769 {A : Type'} (_39023 : A -> Prop) : (term442 A _39023) = (term442 A _39023).
Proof. exact (eq_refl (term442 A _39023)). Qed.
Lemma lem3603770 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term488 A _39023 _39022) = (term495 A _39022 _39023).
Proof. exact (MK_COMB (@lem3603769 A _39023) (@lem3603763 A _39022 _39023)). Qed.
Lemma lem3603774 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3603775 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term495 A _39022 _39023) = (term496 A _39022 _39023).
Proof. exact (@lem3603774 (@I ((A -> Prop) -> Prop) (@FINITE A) _39022) (term440 A _39023) (term438 A _39022 _39023)). Qed.
Lemma lem3603791 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term488 A _39023 _39022) = (term496 A _39022 _39023).
Proof. exact (TRANS (@lem3603770 A _39022 _39023) (@lem3603775 A _39022 _39023)). Qed.
Lemma lem3603792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3603793 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term497 A _39023 _39022) = (term498 A _39022 _39023).
Proof. exact (MK_COMB (@lem3603792) (@lem3603791 A _39022 _39023)). Qed.
Lemma lem3603809 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term496 A _39022 _39023) = (term496 A _39022 _39023).
Proof. exact (eq_refl (term496 A _39022 _39023)). Qed.
Lemma lem3603810 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : ((term488 A _39023 _39022) = (term496 A _39022 _39023)) = ((term496 A _39022 _39023) = (term496 A _39022 _39023)).
Proof. exact (MK_COMB (@lem3603793 A _39022 _39023) (@lem3603809 A _39022 _39023)). Qed.
Lemma lem3603812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3603813 (x : Prop) : (x = x) = True.
Proof. exact (@lem3603812 Prop x). Qed.
Lemma lem3603814 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : ((term496 A _39022 _39023) = (term496 A _39022 _39023)) = True.
Proof. exact (@lem3603813 (term496 A _39022 _39023)). Qed.
Lemma lem3603815 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : ((term488 A _39023 _39022) = (term496 A _39022 _39023)) = True.
Proof. exact (TRANS (@lem3603810 A _39022 _39023) (@lem3603814 A _39022 _39023)). Qed.
Lemma lem3603816 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : True = ((term488 A _39023 _39022) = (term496 A _39022 _39023)).
Proof. exact (SYM (@lem3603815 A _39022 _39023)). Qed.
Lemma lem3603817 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term488 A _39023 _39022) = (term496 A _39022 _39023).
Proof. exact (EQ_MP (@lem3603816 A _39022 _39023) (@lem0)). Qed.
Lemma lem3603818 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) (h1 : term12 A) : term496 A _39022 _39023.
Proof. exact (EQ_MP (@lem3603817 A _39022 _39023) (@lem3603698 A _39023 _39022 h1)). Qed.
Lemma lem3603820 (b : Prop) (a : Prop) : (a \/ b) = (term499 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3603821 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) : (term496 A _39022 _39023) = (term500 A _39023 _39022).
Proof. exact (@lem3603820 (term443 A _39022 _39023) (@I ((A -> Prop) -> Prop) (@FINITE A) _39022)). Qed.
Lemma lem3603823 (a : Prop) (b : Prop) : (term501 a b) = (term502 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3603824 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term503 A _39022 _39023) = (term504 A _39022 _39023).
Proof. exact (@lem3603823 (term440 A _39023) (term438 A _39022 _39023)). Qed.
Lemma lem3603826 (a : Prop) : (term505 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3603827 {A : Type'} (_39023 : A -> Prop) : (term506 A _39023) = (@I ((A -> Prop) -> Prop) (@FINITE A) _39023).
Proof. exact (@lem3603826 (@I ((A -> Prop) -> Prop) (@FINITE A) _39023)). Qed.
Lemma lem3603828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3603829 {A : Type'} (_39023 : A -> Prop) : (term507 A _39023) = (term465 A _39023).
Proof. exact (MK_COMB (@lem3603828) (@lem3603827 A _39023)). Qed.
Lemma lem3603831 (a : Prop) : (term505 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3603832 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term508 A _39022 _39023) = (term436 A _39022 _39023).
Proof. exact (@lem3603831 (term436 A _39022 _39023)). Qed.
Lemma lem3603833 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term504 A _39022 _39023) = (term509 A _39022 _39023).
Proof. exact (MK_COMB (@lem3603829 A _39023) (@lem3603832 A _39022 _39023)). Qed.
Lemma lem3603834 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term503 A _39022 _39023) = (term509 A _39022 _39023).
Proof. exact (TRANS (@lem3603824 A _39022 _39023) (@lem3603833 A _39022 _39023)). Qed.
Lemma lem3603835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3603836 {A : Type'} (_39022 : A -> Prop) (_39023 : A -> Prop) : (term510 A _39022 _39023) = (term511 A _39022 _39023).
Proof. exact (MK_COMB (@lem3603835) (@lem3603834 A _39022 _39023)). Qed.
Lemma lem3603837 {A : Type'} (_39022 : A -> Prop) : (@I ((A -> Prop) -> Prop) (@FINITE A) _39022) = (@I ((A -> Prop) -> Prop) (@FINITE A) _39022).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) (@FINITE A) _39022)). Qed.
Lemma lem3603838 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) : (term500 A _39023 _39022) = (term512 A _39023 _39022).
Proof. exact (MK_COMB (@lem3603836 A _39022 _39023) (@lem3603837 A _39022)). Qed.
Lemma lem3603839 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) : (term496 A _39022 _39023) = (term512 A _39023 _39022).
Proof. exact (TRANS (@lem3603821 A _39023 _39022) (@lem3603838 A _39023 _39022)). Qed.
Lemma lem3603841 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term48 A _39018) (h2 : term368 A _39018 s P) : term513 A _39018 P s.
Proof. exact (conj (@lem3603737 A _39018 s P h2) (@lem3603746 A P s _39018 h1)). Qed.
Lemma lem3603843 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) (h1 : term12 A) : term512 A _39023 _39022.
Proof. exact (EQ_MP (@lem3603839 A _39023 _39022) (@lem3603818 A _39022 _39023 h1)). Qed.
Lemma lem3603844 {A : Type'} (_39023 : A -> Prop) (_39022 : A -> Prop) (h1 : term12 A) : term512 A _39023 _39022.
Proof. exact (@lem3603843 A _39023 _39022 h1). Qed.
Lemma lem3603845 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) : term514 A _39018 s P.
Proof. exact (@lem3603844 A s (term452 A _39018 s P) h1). Qed.
Lemma lem3603848 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) (h2 : term48 A _39018) (h3 : term368 A _39018 s P) : term463 A _39018 s P.
Proof. exact (@lem3603845 A _39018 s P h1 (@lem3603841 A _39018 s P h2 h3)). Qed.
Lemma lem3603849 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) (h2 : term48 A _39018) (h3 : term368 A _39018 s P) : term515 A _39018 s P.
Proof. exact (fun h0 : term464 A _39018 s P => @lem3603848 A _39018 s P h1 h2 h3). Qed.
Lemma lem3603851 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3603852 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term515 A _39018 s P) = (term463 A _39018 s P).
Proof. exact (@lem3603851 (term463 A _39018 s P)). Qed.
Lemma lem3603853 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) (h2 : term48 A _39018) (h3 : term368 A _39018 s P) : term463 A _39018 s P.
Proof. exact (EQ_MP (@lem3603852 A _39018 s P) (@lem3603849 A _39018 s P h1 h2 h3)). Qed.
Lemma lem3603856 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3603858 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) : (term464 A _39018 s P) = (term516 A _39018 s P).
Proof. exact (@lem3603856 (term463 A _39018 s P)). Qed.
Lemma lem3603861 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term368 A _39018 s P) : term516 A _39018 s P.
Proof. exact (EQ_MP (@lem3603858 A _39018 s P) (@lem3603730 A _39018 s P h1)). Qed.
Lemma lem3603864 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) (h2 : term48 A _39018) (h3 : term368 A _39018 s P) : False.
Proof. exact (@lem3603861 A _39018 s P h3 (@lem3603853 A _39018 s P h1 h2 h3)). Qed.
Lemma lem3603865 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) (h2 : term48 A _39018) (h3 : term368 A _39018 s P) : term517.
Proof. exact (fun h0 : ~ False => @lem3603864 A _39018 s P h1 h2 h3). Qed.
Lemma lem3603867 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3603868 : term517 = False.
Proof. exact (@lem3603867 False). Qed.
Lemma lem3603869 {A : Type'} (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term12 A) (h2 : term48 A _39018) (h3 : term368 A _39018 s P) : False.
Proof. exact (EQ_MP (@lem3603868) (@lem3603865 A _39018 s P h1 h2 h3)). Qed.
Lemma lem3603870 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term131 _84465 _39019) (h2 : term12 A) (h3 : term48 A _39018) (h4 : term368 A _39018 s P) : False.
Proof. exact (ex_elim (@lem3601483 _84465 _39019 h1) (fun x' : type635 _84465 => fun h0 : term365 _84465 _39019 x' => @lem3603869 A _39018 s P h2 h3 h4)). Qed.
Lemma lem3603871 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (s : A -> Prop) (P : A -> Prop) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term48 A _39018) (h5 : term368 A _39018 s P) : False.
Proof. exact (ex_elim (@lem3602101 A _39018 h2) (fun x : type635 A => fun h0 : term365 A _39018 x => @lem3603870 _84465 A _39019 _39018 s P h1 h3 h4 h5)). Qed.
Lemma lem3603872 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (s : A -> Prop) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term48 A _39018) (h5 : term377 A _39018 s) : False.
Proof. exact (ex_elim (@lem3602562 A _39018 s h5) (fun P : A -> Prop => fun h0 : term376 A _39018 s P => @lem3603871 _84465 A _39019 _39018 s P h1 h2 h3 h4 h0)). Qed.
Lemma lem3603873 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term48 A _39018) (h5 : term72 A _39018) : False.
Proof. exact (ex_elim (@lem3602213 A _39018 h5) (fun s : A -> Prop => fun h0 : term382 A _39018 s => @lem3603872 _84465 A _39019 _39018 s h1 h2 h3 h4 h0)). Qed.
Lemma lem3603874 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term48 A _39018) (h5 : term72 A _39018) : (term48 A _39018) = False.
Proof. exact (prop_ext (fun h6 : term48 A _39018 => @lem3603873 _84465 A _39019 _39018 h1 h2 h3 h4 h5) (fun h6 : False => @lem3602561 A _39018 h4)). Qed.
Lemma lem3603875 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term48 A _39018) (h5 : term72 A _39018) : False.
Proof. exact (EQ_MP (@lem3603874 _84465 A _39019 _39018 h1 h2 h3 h4 h5) (@lem3602561 A _39018 h4)). Qed.
Lemma lem3603876 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term72 A _39018) : term518 A _39018.
Proof. exact (fun h0 : term48 A _39018 => @lem3603875 _84465 A _39019 _39018 h1 h2 h3 h0 h4). Qed.
Lemma lem3603877 {A : Type'} (_39018 : type636 A) : (term518 A _39018) = (term49 A _39018).
Proof. exact (@lem69 (term48 A _39018)). Qed.
Lemma lem3603878 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term72 A _39018) : term49 A _39018.
Proof. exact (EQ_MP (@lem3603877 A _39018) (@lem3603876 _84465 A _39019 _39018 h1 h2 h3 h4)). Qed.
Lemma lem3603879 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term12 A) (h4 : term72 A _39018) : term137 _84465 A _39019 _39018.
Proof. exact (fun h0 : term48 _84465 _39019 => @lem3603878 _84465 A _39019 _39018 h1 h2 h3 h4). Qed.
Lemma lem3603880 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term72 A _39018) : term138 _84465 A _39019 _39018.
Proof. exact (fun h0 : term12 A => @lem3603879 _84465 A _39019 _39018 h1 h2 h0 h3). Qed.
Lemma lem3603881 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) (h3 : term72 A _39018) : term139 _84465 A _39019 _39018.
Proof. exact (fun h0 : term12 _84465 => @lem3603880 _84465 A _39019 _39018 h1 h2 h3). Qed.
Lemma lem3603882 {_84465 A : Type'} (_39019 : type636 _84465) (_39018 : type636 A) (h1 : term131 _84465 _39019) (h2 : term131 A _39018) : term140 _84465 A _39019 _39018.
Proof. exact (fun h0 : term72 A _39018 => @lem3603881 _84465 A _39019 _39018 h1 h2 h0). Qed.
Lemma lem3603883 {_84465 A : Type'} (_39018 : type636 A) (_39019 : type636 _84465) (h1 : term131 _84465 _39019) : term141 _84465 A _39019 _39018.
Proof. exact (fun h0 : term131 A _39018 => @lem3603882 _84465 A _39019 _39018 h1 h0). Qed.
Lemma lem3603888 {_84465 A : Type'} (_39019 : type636 _84465) (h1 : term131 _84465 _39019) : term143 _84465 A _39019.
Proof. exact (fun _39018 : type636 A => @lem3603883 _84465 A _39018 _39019 h1). Qed.
Lemma lem3603889 {_84465 A : Type'} (_39019 : type636 _84465) : term163 _84465 A _39019.
Proof. exact (fun h0 : term131 _84465 _39019 => @lem3603888 _84465 A _39019 h0). Qed.
Lemma lem3603894 {_84465 A : Type'} : term165 _84465 A.
Proof. exact (fun _39019 : type636 _84465 => @lem3603889 _84465 A _39019). Qed.
Lemma lem3603895 {_84465 A : Type'} : term13 _84465 A.
Proof. exact (EQ_MP (@lem3600858 _84465 A) (@lem3603894 _84465 A)). Qed.
Lemma lem3603897 {_84465 A : Type'} : term13 _84465 A.
Proof. exact (@lem3599962 _84465 A (@lem3603895 _84465 A)). Qed.
Lemma lem3603898 {_84465 A : Type'} (h1 : term10 A) : term25 _84465 A.
Proof. exact (@lem3603897 _84465 A (@lem3599939 A h1)). Qed.
Lemma lem3603899 {_84465 A : Type'} (h1 : term10 A) : term23 _84465 A.
Proof. exact (@lem3603898 _84465 A h1 (@lem3599946 _84465)). Qed.
Lemma lem3603900 {_84465 A : Type'} (h1 : term10 A) : term20 _84465 A.
Proof. exact (@lem3603899 _84465 A h1 (@lem3599944 A)). Qed.
Lemma lem3603901 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem3603900 Prop A h1 (@lem3221162 Prop)). Qed.
Lemma lem3603902 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem3603901 A h1 (@lem3599940 A)). Qed.
Lemma lem3603903 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem3603902 A h1) (fun h2 : False => @lem3599939 A h1)). Qed.
Lemma lem3603904 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem3603903 A h1) (@lem3599939 A h1)). Qed.
Lemma lem3603905 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem3603904 A h0). Qed.
Lemma lem3603906 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3599938 A) (@lem3603905 A)). Qed.
