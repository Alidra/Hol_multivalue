Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_RESTRICT_SET_term_abbrevs.
Require Import ITERATE_RESTRICT_SET_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7156963 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7156965 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7156966 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7156965 A B h1 op). Qed.
Lemma lem7156967 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7156968 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7156967 A B op) (@lem7156966 A B op h1)). Qed.
Lemma lem7156969 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7156970 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7156968 A B op h1 (@lem7156969 B op h2)). Qed.
Lemma lem7156971 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7156970 A B op h0 h1). Qed.
Lemma lem7156972 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7156973 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7156971 A B op h2 (@lem7156972 A B h1)). Qed.
Lemma lem7156974 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7156973 A B op h1 h0). Qed.
Lemma lem7156975 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7156974 A B op h1). Qed.
Lemma lem7156976 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7156975 A B h0). Qed.
Lemma lem7156977 {A B : Type'} : term0 A B.
Proof. exact (@lem7156976 A B (@lem5986609 A B)). Qed.
Lemma lem7156978 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7156977 A B op). Qed.
Lemma lem7156979 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7156981 (h1 : (@neutral real real_add) = term6) : (@neutral real real_add) = term6.
Proof. exact (h1). Qed.
Lemma lem7156982 (h1 : (@neutral real real_add) = term6) : term6 = (@neutral real real_add).
Proof. exact (SYM (@lem7156981 h1)). Qed.
Lemma lem7156983 (h1 : term6 = (@neutral real real_add)) : term6 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7156984 (h1 : term6 = (@neutral real real_add)) : (@neutral real real_add) = term6.
Proof. exact (SYM (@lem7156983 h1)). Qed.
Lemma lem7156985 : ((@neutral real real_add) = term6) = (term6 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term6 => @lem7156982 h1) (fun h1 : term6 = (@neutral real real_add) => @lem7156984 h1)). Qed.
Lemma lem7157002 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7157003 {_133899 : Type'} : (@sum _133899) = (@iterate real _133899 real_add).
Proof. exact (@lem7157002 _133899). Qed.
Lemma lem7157010 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term7 _133899 s P) = (term7 _133899 s P).
Proof. exact (eq_refl (term7 _133899 s P)). Qed.
Lemma lem7157011 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term8 _133899 s P) = (term9 _133899 s P).
Proof. exact (MK_COMB (@lem7157003 _133899) (@lem7157010 _133899 s P)). Qed.
Lemma lem7157012 {_133899 : Type'} (f : _133899 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7157013 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term10 _133899 s P f) = (term11 _133899 s P f).
Proof. exact (MK_COMB (@lem7157011 _133899 s P) (@lem7157012 _133899 f)). Qed.
Lemma lem7157014 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157015 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term12 _133899 s P f) = (term13 _133899 s P f).
Proof. exact (MK_COMB (@lem7157014) (@lem7157013 _133899 s P f)). Qed.
Lemma lem7157017 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7157018 {_133899 : Type'} : (@sum _133899) = (@iterate real _133899 real_add).
Proof. exact (@lem7157017 _133899). Qed.
Lemma lem7157019 {_133899 : Type'} (s : _133899 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7157020 {_133899 : Type'} (s : _133899 -> Prop) : (@sum _133899 s) = (@iterate real _133899 real_add s).
Proof. exact (MK_COMB (@lem7157018 _133899) (@lem7157019 _133899 s)). Qed.
Lemma lem7157022 : term6 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7156985) (@lem7065438)). Qed.
Lemma lem7157023 {_133899 : Type'} (P : _133899 -> Prop) (f : _133899 -> real) (x : _133899) : (term14 _133899 P f x) = (term14 _133899 P f x).
Proof. exact (eq_refl (term14 _133899 P f x)). Qed.
Lemma lem7157024 {_133899 : Type'} (P : _133899 -> Prop) (f : _133899 -> real) (x : _133899) : (term15 _133899 P f x) = (term16 _133899 P f x).
Proof. exact (MK_COMB (@lem7157023 _133899 P f x) (@lem7157022)). Qed.
Lemma lem7157025 {_133899 : Type'} (P : _133899 -> Prop) (f : _133899 -> real) : (term17 _133899 P f) = (term18 _133899 P f).
Proof. exact (fun_ext (fun x : _133899 => @lem7157024 _133899 P f x)). Qed.
Lemma lem7157026 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term19 _133899 s P f) = (term20 _133899 s P f).
Proof. exact (MK_COMB (@lem7157020 _133899 s) (@lem7157025 _133899 P f)). Qed.
Lemma lem7157027 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : ((term10 _133899 s P f) = (term19 _133899 s P f)) = ((term11 _133899 s P f) = (term20 _133899 s P f)).
Proof. exact (MK_COMB (@lem7157015 _133899 s P f) (@lem7157026 _133899 s P f)). Qed.
Lemma lem7157030 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term21 _133899 s P) = (term22 _133899 s P).
Proof. exact (fun_ext (fun f : _133899 -> real => @lem7157027 _133899 s P f)). Qed.
Lemma lem7157031 {_133899 : Type'} : (@all (_133899 -> real)) = (@all (_133899 -> real)).
Proof. exact (eq_refl (@all (_133899 -> real))). Qed.
Lemma lem7157032 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term23 _133899 s P) = (term24 _133899 s P).
Proof. exact (MK_COMB (@lem7157031 _133899) (@lem7157030 _133899 s P)). Qed.
Lemma lem7157037 {_133899 : Type'} (P : _133899 -> Prop) : (term25 _133899 P) = (term26 _133899 P).
Proof. exact (fun_ext (fun s : _133899 -> Prop => @lem7157032 _133899 s P)). Qed.
Lemma lem7157038 {_133899 : Type'} : (@all (_133899 -> Prop)) = (@all (_133899 -> Prop)).
Proof. exact (eq_refl (@all (_133899 -> Prop))). Qed.
Lemma lem7157039 {_133899 : Type'} (P : _133899 -> Prop) : (term27 _133899 P) = (term28 _133899 P).
Proof. exact (MK_COMB (@lem7157038 _133899) (@lem7157037 _133899 P)). Qed.
Lemma lem7157044 {_133899 : Type'} : (term29 _133899) = (term30 _133899).
Proof. exact (fun_ext (fun P : _133899 -> Prop => @lem7157039 _133899 P)). Qed.
Lemma lem7157045 {_133899 : Type'} : (@all (_133899 -> Prop)) = (@all (_133899 -> Prop)).
Proof. exact (eq_refl (@all (_133899 -> Prop))). Qed.
Lemma lem7157046 {_133899 : Type'} : (term31 _133899) = (term32 _133899).
Proof. exact (MK_COMB (@lem7157045 _133899) (@lem7157044 _133899)). Qed.
Lemma lem7157051 {_133899 : Type'} : (term32 _133899) = (term31 _133899).
Proof. exact (SYM (@lem7157046 _133899)). Qed.
Lemma lem7157053 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7156979 A B op) (@lem7156978 A B op)). Qed.
Lemma lem7157054 {_133899 : Type'} (op : type1627) : term33 _133899 op.
Proof. exact (@lem7157053 _133899 real op). Qed.
Lemma lem7157055 {_133899 : Type'} : term34 _133899.
Proof. exact (@lem7157054 _133899 real_add). Qed.
Lemma lem7157057 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7156963) (@lem7067132)). Qed.
Lemma lem7157058 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7157057)). Qed.
Lemma lem7157059 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7157058) (@lem0)). Qed.
Lemma lem7157060 {_133899 : Type'} : term32 _133899.
Proof. exact (@lem7157055 _133899 (@lem7157059)). Qed.
Lemma lem7157061 {_133899 : Type'} : term31 _133899.
Proof. exact (EQ_MP (@lem7157051 _133899) (@lem7157060 _133899)). Qed.
