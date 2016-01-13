(*
Copyright (c) 2007-2011.

Authors: Levent Erkok (erkokl@gmail.com)
         John Matthews (matthews.r.john@gmail.com)

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the developers nor the names of its contributors may
      be used to endorse or promote products derived from this software without
      specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* 
Version history:

Version 1.0  [Nov 2007]: Initial release, works with Isabelle 2007
Version 1.1  [Jun 2008]: Updated to work with Isabelle 2008 
Version 1.2  [Jul 2008]: More careful handling of nat's
Version 1.3  [Sep 2010]: Updated to work with Isabelle 2009-2
Version 1.4  [Mar 2011]: Updated to work with Isabelle 2011
*)

theory ISMT
imports Main 
begin

ML
{*
signature PIPE_PROCESS =
sig
  type Process;

  val launch             : string * string list -> Process;
  val kill               : Process -> unit;

  val instream_of        : Process -> TextIO.instream;
  val outstream_of       : Process -> TextIO.outstream;

  val charReady          : Process -> bool;

  val flush              : Process -> unit;

  (* Doesn't flush output pipe *)
  val outputList         : Process * string * string * string *
                           ('a -> string) * 'a list -> unit;

  (* Flushes output pipe *)
  val outputLines        : Process * string list -> unit;

  (* Reads the next line from instream. This is
  ** a blocking operation.
  *)
  val readLine : Process -> string

  val readLinesUntilChar : Process * char *
                           (string * 'a -> 'a) *
                           (string * 'a -> 'a) *
                           'a -> 'a;
  val linesUntilChar     : Process * char -> string list
  val linesUntilResponse : Process * string -> string list
  val linesUntilOneOf    : Process * string list -> string list

  (* same as linesUntilOneOf, except last line doesn't have to end with '\n' *)
  val linesUntilOneOfPartial : Process * string list -> string list

  (* Read lines that are currently queued up on the input stream.
  ** This is (supposed to be) a non-blocking operation, provided
  ** that the final pending character (if any) in the input stream
  ** is a newline.
  *)
  val pendingLines : Process -> string list
end;
  
structure PipeProcess : PIPE_PROCESS =
struct

type Process = (TextIO.instream, TextIO.outstream) Unix.proc *
	       TextIO.instream *
	       TextIO.outstream;

fun launch (processName,args)
    = let val mp = Unix.execute (processName,args);
	  val (inStream,outStream) = Unix.streamsOf mp
      in (mp, inStream, outStream)
      end;

fun kill proc
    = let val p = #1 proc;
          val _ = Unix.kill (p, Posix.Signal.quit);
          val _ = Unix.reap p in   (* Waits until process has terminated,
                                   ** then removes the zombie process
                                   ** from the process id table.
                                   *)
          ()
      end;

fun instream_of proc  = #2 proc;
fun outstream_of proc = #3 proc;

(** Checks to see whether at least one character is available to read from
 **  the input stream.
 **)
fun charReady proc
    = case TextIO.canInput (instream_of proc, 1) of
        NONE => false
      | SOME _ => true;

fun flush proc
    = TextIO.flushOut (outstream_of proc);

fun outputList (proc, beginStr, sepStr, endStr, elemToStr, xs)
    = let val ostrm = outstream_of proc
          fun outLines []
              = if endStr <> "" then TextIO.output (ostrm,endStr) else ()
            | outLines [x]
              = (TextIO.output (ostrm, elemToStr x);
                 outLines [])
            | outLines (x::xs)
              = (TextIO.output (ostrm, elemToStr x);
		 (if sepStr <> "" then TextIO.output (ostrm,sepStr) else ());
		 outLines xs);
           val _ = (if beginStr <> "" then TextIO.output (ostrm, beginStr)
                    else ()) in
           outLines xs
      end;

fun outputLines (proc, lines)
    = let val newline = str #"\n";
          fun id str = str;
          val _ = outputList (proc, "", newline, newline, id, lines) in
          flush proc
      end;

fun readLine proc
    = case TextIO.inputLine (instream_of proc) of
      	     NONE   => ""
	   | SOME s => s

fun readAllPending proc
    = case TextIO.canInput (instream_of proc, 1) of
	  NONE   => ""
	| SOME 0 => ""
	| SOME i => TextIO.inputN (instream_of proc, i) ^ readAllPending proc

(** Read lines from instr, applying lnFn to each line read until
 ** it reads a line that satisfies the 'final' predicate.
 **)
fun readLinesUntil (proc, final, lnFn, lastFn, init)
    = let fun readLines x
              = let val line = readLine proc in
                if final line then lastFn (line,x)
		else readLines (lnFn (line,x))
		end
      in readLines init
      end;

(** Specialized version where all we look for is a beginning character **)
fun readLinesUntilChar (proc, char, lnFn, lastFn, init)
    = readLinesUntil (proc, (fn ln => String.sub (ln, 0) = char), lnFn, lastFn, init);

(** part of user interface; read until a line that starts with a char: **)
fun linesUntilChar (proc,char)
    = readLinesUntilChar (proc, char, (op ::), (fn (l,ls) => rev (l::ls)),[]);

(** OR, read until a line looks exactly like: **)
fun linesUntilResponse (proc, str)
    = readLinesUntil (proc, (fn ln => ln = str), (op ::), (fn (l, ls) => rev (l::ls)), []);

(** OR, read until a line looks exactly like one of: **)
fun linesUntilOneOf (proc, strs)
    = readLinesUntil (proc, (fn ln => List.exists (fn s => ln = s) strs), (op ::), (fn (l, ls) => rev (l::ls)), []);

fun pendingLines proc
    = let fun plines lines
              = if charReady proc then plines (readLine proc :: lines)
                else lines in
          rev (plines [])
      end;

(* same as linesUntilOneOf, however, the last line doesn't have to end with '\n'. Note that this
   will eat-up all the available input, and it will block until it gets the desired output! *)
fun linesUntilOneOfPartial (proc, strs)
    = let fun rl sofar = let val lines = Library.filter (fn s => s <> "") (Library.split_lines (readAllPending proc))
                             val patterns = map String.explode strs
			 in if lines = [] 
			    then rl sofar
			    else let val lastLine = String.explode (List.last lines)
				 in if Library.exists (fn s => Library.is_prefix (op =) s lastLine) patterns
				    then sofar @ lines
				    else rl (sofar @ lines)
				 end
			 end
      in rl []
      end
end;



*}

ML
{*
(** TermUtils.Ml: util functions for various term related goodies
 ** Date:   Mar 6th, 2007.
 **)
structure TermUtils =
struct

fun conc_of (t : Term.term) : Term.term
  = case t of
      (Const ("==>", _) $ _ $ r) => conc_of r
    | t => t;

local
    fun wrap b a i  = b ^ i ^ a
    val quote   = wrap "\"" "\""
    val paren   = wrap "(" ")"
    val sqparen = wrap "[" "]"
    val pList   = paren o commas
    val sList   = sqparen o commas
in
fun showSrt ss = sList (map quote ss)
fun showTyp (Type  (s, ts))  = "Type "  ^ pList [quote s, sList (map showTyp ts)]
  | showTyp (TFree (s, srt)) = "TFree " ^ pList [quote s, showSrt srt]
  | showTyp (TVar  (i, srt)) = "TVar "  ^ pList [Term.string_of_vname i, showSrt srt]
and showTerm (Const (s, t))    = "Const " ^ pList [quote s, showTyp t]
  | showTerm (Free  (s, t))    = "Free "  ^ pList [quote s, showTyp t]
  | showTerm (Var   (i, t))    = "Var "   ^ pList [Term.string_of_vname i, showTyp t]
  | showTerm (Bound i)         = "Bound " ^ Int.toString i
  | showTerm (Abs   (s, T, t)) = "Abs "   ^ pList [quote s, showTyp T, showTerm t]
  | showTerm (t1 $ t2)         = paren (showTerm t1) ^ " $ " ^ paren (showTerm t2)
end
	
end; (* struct TermUtils *)
*}

ML
{*
(* ResourceTimer.ML: A general structure for measuring (nested) elapsed time  *)
(*                   A timer can properly be nested, with no problem, i.e.,   *)
(*                   It's OK to say:                                          *)
(*                       withTimer1 t f a                                     *)
(*                   where f itself starts/stops the timer t as well.         *)
(*                                                                            *)
(* Date: Jan. 8th, 2007                                                       *)

signature RESOURCE_TIMER =
sig

type T;

val newTimer   : unit -> T;
val reset      : T -> unit;
val elapsed    : T -> LargeInt.int; (* turn it into milliseconds *)
val withTimer1 : T -> ('a -> 'b) -> ('a -> 'b);
val withTimer2 : T -> ('a -> 'b -> 'c) -> ('a -> 'b -> 'c);
val withTimer3 : T -> ('a -> 'b -> 'c -> 'd) -> ('a -> 'b -> 'c -> 'd);
val withTimer4 : T -> ('a -> 'b -> 'c -> 'd -> 'e) -> ('a -> 'b -> 'c -> 'd -> 'e);

(* one-shot measurements, with no explicit timer creation needed: *)
val runWithTimer : ('a -> 'b) -> ('a -> (LargeInt.int * 'b));
end; (* signature RESOURCE_TIMER *)

structure ResourceTimer : RESOURCE_TIMER =
struct

open Unsynchronized

type T = Time.time ref * Time.time ref * int ref; (* Accumulated time * current time * nesting *)

fun newTimer  ()           = (ref Time.zeroTime, ref (Time.now()), ref 0);
fun start     (_,   t0, n) = if !n = 0 then (t0 := Time.now(); n := 1) else n := !n + 1;
fun stop      (acc, t0, n) = if !n = 1 
			     then let val t1 = Time.now() 
				  in acc := !acc + t1 - !t0; 
	 			     t0 := t1;
				     n  := 0
				  end
			     else if !n < 0 
			     then error ("ResourceTimer.stop: impossible happened, n < 0!")
			     else n := !n - 1;
fun reset     (acc, t0, n) = if !n <> 0 
			     then error ("ResourceTimer.reset: Cannot reset a running timer!")
			     else (acc := Time.zeroTime; t0 := Time.now());
fun elapsed   (acc,  _, _) = Time.toMilliseconds (!acc);

fun withTimer1 t f a       = (start t; let val r = f a;       in stop t; r end) handle e => (stop t; raise e);
fun withTimer2 t f a b     = (start t; let val r = f a b;     in stop t; r end) handle e => (stop t; raise e);
fun withTimer3 t f a b c   = (start t; let val r = f a b c;   in stop t; r end) handle e => (stop t; raise e);
fun withTimer4 t f a b c d = (start t; let val r = f a b c d; in stop t; r end) handle e => (stop t; raise e);

fun runWithTimer f a       = let val t   = newTimer (); 
			         val res = withTimer1 t f a; 
			     in stop t;	
				(elapsed t, res) 
			     end;
end; (* structure ResourceTimer *)
*}
ML
{*
(* ISMTInterface.ML: Tactics for using incremental SMT solvers from Isabelle
** Date: Mar. 9th, 2007
*)

datatype 'model Result = UNSAT | SAT of 'model | UNKNOWN of 'model

open Unsynchronized

signature ISMT_SIG = 
sig
  type Options
  
  (* Configuration *)
  val ismt_trace          : bool ref          (* Print debugging data *)
  val ismt_tcheck         : bool ref          (* Enable backend-type checking *)
  val ismt_stats          : bool ref          (* Enable statistics collection/printing *)
  val ismt_debug          : bool ref          (* Run in debug mode *)
  val ismt_addAccessor    : Term.term -> unit (* Install an accessor function *)

  (* Entry point *)
  val ismtSolver  : Context.theory -> Options * Term.term -> Term.term
end (* signature ISMT_SIG *)

signature ISMTBackend_SIG =
sig
  type Script
  type Model
  type Options =   Context.theory (* theory to interpret things in *)
                 * string option  (* dump file *)
		 * bool           (* should type check? *)
                 * bool           (* should turn debugging on? *)

  val addAccessor  : Term.term -> unit
  val identifier   : string
  val init         : Options -> unit;
  val fromIsabelle : Term.term -> Script
  val explainModel : Model -> string * string
  val decide       : Script -> Model Result
end (* signature ISMTSolver_SIG *)

functor ISMTInterface(structure backend : ISMTBackend_SIG) : ISMT_SIG =
struct

  open Unsynchronized

  type Options = string option * bool option * bool option * bool option 

  (* Initial configuration *)
  val ismt_trace    = ref false
  val ismt_tcheck   = ref true
  val ismt_stats    = ref false
  val ismt_debug    = ref false  

  val ismt_addAccessor    = backend.addAccessor

  fun reportStats (yices, total)
    = let val trans  = total - yices
	  val rtotal = Real.fromInt total
	  val ptrans = 100.0 *  (Real.fromInt trans / rtotal)
	  val pyices = 100.0 *  (Real.fromInt yices / rtotal)
	  fun ppt r  = StringCvt.padLeft #" " 6 (LargeInt.toString r)
	  fun ppc r  = StringCvt.padLeft #" " 6 (Real.fmt (StringCvt.FIX (SOME 2)) r)
	  val solver = backend.identifier 
	  fun ppl s  = StringCvt.padLeft #" " (size solver + 4) s
      in 
	  writeln "STATISTICS: (in milliseconds)";
	  writeln (ppl "Trans: "       ^ ppt trans ^ "\t(" ^ ppc ptrans ^ "%)");
	  writeln (ppl (solver ^ ": ") ^ ppt yices ^ "\t(" ^ ppc pyices ^ "%)");
	  writeln (ppl "Total: "       ^ ppt total ^ "\t(100.00%)")
      end

  fun ismtSolver thy ((mbDump, mbTC, mbStats, mbDebug), trm) =
      let fun explain model = let val (ce, ui) = backend.explainModel model
			      in Library.prefix_lines "    " ce ^ "\nUninterpreted Constants of the counter-example:\n" ^ Library.prefix_lines "    " ui
			      end
	  fun run () = let val script = (backend.init (thy, mbDump, Option.getOpt (mbTC, !ismt_tcheck), Option.getOpt (mbDebug, !ismt_debug)); 
					 backend.fromIsabelle trm)
			   val (solverTime, res) = ResourceTimer.runWithTimer backend.decide script
		       in (solverTime, res)
		       end
          val (totalTime, (solverTime, res)) = ResourceTimer.runWithTimer run ()
	  val statsMode = Option.getOpt (mbStats, !ismt_stats)
      in 
	  (case res of
	     UNSAT         => (if statsMode then reportStats (solverTime, totalTime) else (); trm)
	   | SAT model     => raise THM ("A counter-example is found:\n" ^ explain model, 0, [])
	   | UNKNOWN model => raise THM (backend.identifier ^ " couldn't decide the subgoal! Potential counter-example:\n" 
							    ^ explain model, 0, [])
	  )
	  handle e => (if statsMode then reportStats (solverTime, totalTime) else ();
	               raise e)
      end

end  (* struct ISMT *)
*}

ML
{*
(* A version of Pretty that ensures everything is plain *)
structure PPR =
struct
 val mode                 = []
 fun plainPrint printer d = Print_Mode.setmp mode printer d
 val string_of            = plainPrint Pretty.string_of
 val keyword              = plainPrint Pretty.keyword
 val brk                  = plainPrint Pretty.brk
 val blk                  = plainPrint Pretty.blk
 val str                  = plainPrint Pretty.str
 val breaks               = plainPrint Pretty.breaks
 val enclose              = plainPrint Pretty.enclose
end
*}

ML
{*
structure Util =
struct
  open List

  fun concatMap  f = foldr (op @) [] o map f 
  fun stringyMap f = Library.space_implode " " o map f
  fun splitAt n lst 
      = let fun s 0 lst     = ([], lst)
	      | s _ []      = ([], [])
	      | s n (x::xs) = let val (xs', xs'') = s (n-1) xs in (x::xs', xs'') end
	in if n < 0 then error ("splitAt called with negative argument: " ^ Int.toString n)
	   else s n lst
	end
  fun butLast xs = #1 (Library.split_last xs)
  fun last xs    = List.last xs

  val currentTheory   : Context.theory ref   = ref (@{theory});
  val shouldTypeCheck : bool ref             = ref true
  val mbDumpFile      : (string option) ref  = ref NONE
  val shouldDebug     : bool ref             = ref false

  fun trace f = if (!shouldDebug) then tracing ("### " ^ f ()) else ()

  fun initGlobals (thy, mbFile, tc, debug)  = 
      (currentTheory   := thy;
       mbDumpFile      := mbFile;
       shouldTypeCheck := tc;
       shouldDebug     := debug)

  fun interfaceMessage s
     = case !mbDumpFile of
	   NONE     => ()
         | SOME "-" => ()
         | SOME f   => let val stream = TextIO.openAppend f
                       in TextIO.output (stream, "\n" ^ Library.prefix_lines ";;; " s);
		          TextIO.output (stream, "\n");
    			  TextIO.flushOut stream;
			  TextIO.closeOut stream
		       end
	   handle _ => warning ("Unable to write to the dump file! (" ^ s ^ ")")

  fun interfaceError   s = (interfaceMessage s; raise (Fail s))
  fun interfaceWarning s = (interfaceMessage s; if (!shouldDebug) then warning s else ())

  fun dumpScript script 
    = case !mbDumpFile of
	 NONE     => ()
       | SOME "-" => List.app writeln (split_lines script)
       | SOME f   => let val stream = TextIO.openOut f
		     in TextIO.output (stream, script);
    			TextIO.flushOut stream;
		        TextIO.closeOut stream
		     end
	             handle _ => warning ("Failed to write the Yices output to the file: " ^ f)

  fun dumpResults res explainModel
    = let fun outModel stream msg1 msg2 model
	    = let val pref = Library.prefix_lines ";;;    "
		  fun explain []   = ["(No explicit model returned from Yices.)"]
		    | explain mods = map #1 mods
		  val mods  = pref (Library.space_implode "\n" (explain (fst model)))
		  val (hmods, hunints) = let val (m, u) = explainModel model in (pref m, pref u) end
	      in TextIO.output(stream, ";;; " ^ msg1 ^ ":\n" ^ mods ^ "\n;;;\n");
		 TextIO.output(stream, ";;; " ^ msg2 ^ ":\n" ^ hmods ^ "\n;;;\n");
		 TextIO.output(stream, ";;; Uninterpreted Constants of the counter-example:\n" ^ hunints ^ "\n")
	      end
      in case !mbDumpFile of
             NONE     => ()
	   | SOME "-" => ()
	   | SOME f   => let val stream = TextIO.openAppend f
       			 in (case res of
				 UNSAT         => TextIO.output (stream, ";;; Status: Theorem\n")
			       | UNKNOWN model => outModel stream "Unknown, Potential counter-example follows" "Potential HOL Counter-example" model
			       | SAT model     => outModel stream "Falsifiable" "HOL Counter-example" model);
		             TextIO.flushOut stream;
		             TextIO.closeOut stream
			 end 
	     handle _ => warning ("Failed to write results to the Yices output file: " ^ f)
      end
end (* Util *)

signature NAME = 
sig
  eqtype name

  val toString  : name   -> string
  val toName    : string -> name
  val lift      : string -> name
  val incrIndex : name   -> name
  val prefixOf  : name   -> string
  val indexOf   : name   -> int
  val construct : (string * int) -> name
end (* NAME *)

structure Name : NAME = 
struct
  type name = string * int

  fun toString (s, 0) = s
    | toString (s, i) = s ^ "_" ^ Int.toString i

  fun lift s = (s, 0)
  val construct = I

  fun toName s 
    = let val sl = String.explode s
	  val pos = Library.find_index (fn c => c = #"_") (List.rev sl)
      in if pos < 0 then (s, 0)
	 else let val (nm_, i) = Library.take_suffix (fn c => c <> #"_") sl
	          val nm = Util.butLast nm_
	      in if i <> [] andalso List.all Char.isDigit i
		 then (String.implode nm, Option.valOf (Int.fromString (String.implode i)))
		 else (s, 0)
	      end
      end

  fun incrIndex (s, i) = (s, i+1)
  val prefixOf = #1
  val indexOf  = #2
end (* Name *)

signature YICESBRIDGE =
sig
  val issue       : PipeProcess.Process -> string option -> string list
  val sendWhileOK : PipeProcess.Process -> string list -> bool
  val check       : PipeProcess.Process -> string list Result 
end (* YICESBRIDGE *)

structure YicesBridge : YICESBRIDGE = 
struct

  (* Yices configuration *)
  structure YicesParams = 
  struct
    val prompt      = "yices > "
    val statusCmd   = "(status)"
    val statusOK    = "ok"
    val statusNotOK = "unsat"
    val checkCmd    = "(check)"
    val checkSAT    = "sat"
    val checkUnSAT  = "unsat"
    val checkOther  = "unknown"
    val echoPrompt  = "(echo \"" ^ prompt ^ "\")"
    val errorLine   = "Error:"
  end

  fun issue yices mbCmd
    = let val (cmd, toYices) = 
	      case mbCmd of
		  SOME s => (Util.trace (fn _ => "---> Yices: [" ^ s ^ "]"); (s, [s, YicesParams.echoPrompt]))
		| NONE   => ("(none)", [YicesParams.echoPrompt])
	  val _     = (PipeProcess.outputLines (yices, toYices);
		       PipeProcess.flush yices)
	  fun trimS []             = []
	    | trimS (s as (c::cs)) = if Char.isSpace c then trimS cs else s
	  fun trim s = String.implode (List.rev (trimS (List.rev (trimS (String.explode s)))))
	  val lines = List.filter (fn s => s <> "") 
                                  (List.map trim (PipeProcess.linesUntilOneOfPartial (yices, [YicesParams.prompt, YicesParams.errorLine])))
	  val WARNINGL = String.explode "WARNING"
          val ERRORL   = String.explode YicesParams.errorLine
	  fun isWarning s = if Library.is_prefix (op =) WARNINGL (String.explode s) then (Util.interfaceWarning s; true) else false
	  fun isError   s = Library.is_prefix (op =) ERRORL (String.explode s) 
      in  if Library.exists isError lines
	  then lines
	  else case lines of
		   []  => Util.interfaceError ("No valid responses received for command " ^ cmd)
		 | lst => let val res = Util.butLast lst  (* get rid of the final prompt *)
			  in if res <> [] then Util.trace (fn _ => "<--- Yices: [" ^ commas res ^ "]") else ();
			     List.filter (not o isWarning) res
			  end
      end

  fun issueAndCheck yices c
    = let val resp = issue yices (SOME c)
      in if resp = [] then true
	 else if resp = [YicesParams.checkUnSAT] then false
	 else if resp = [YicesParams.checkSAT] then true
	 else Util.interfaceError ("Unexpected response received for command " ^ c ^ ": " ^ commas (List.filter (fn l => l <> "") resp))
      end
  
  fun sendWhileOK yices cmds
    = let fun swok []      = true
	    | swok (c::cs) = if issueAndCheck yices c then swok cs else false
      in swok cmds
      end

  (* sometimes Yices prints counter-examples over multiple lines; this routine joins the lines appropriately
     so that we have one counter-example per line *)
  fun combine lines
    = let fun count []      sofar = sofar
	    | count (x::xs) sofar = count xs (if x = #"(" then (sofar + 1) else if x = #")" then (sofar - 1) else sofar)
	  fun isBalanced line = count (String.explode line) 0 = 0
	  fun comb []         = []
	    | comb [l]        = [l]
	    | comb (x::y::ys) = if isBalanced x then x :: comb (y::ys)
				else comb ((x ^ " " ^ y)::ys)
      in comb lines
      end

  fun check yices
    = let val resp = issue yices (SOME YicesParams.checkCmd)
      in if resp = [YicesParams.checkUnSAT]
	 then UNSAT
	 else case resp of
		  []          => Util.interfaceError ("Yices didn't respond to the check command")
		| (ans::rest) => if ans = YicesParams.checkSAT
				 then SAT (combine rest)
				 else UNKNOWN (combine rest)
      end
end (* YicesBridge *)

(* Intermediate language of s-expressions and types *)
structure IL = 
struct

open List

  datatype Stype = BasicType of Name.name
		 | Uninterpreted of Name.name
		 | FuncType of Stype list      
		 | TupleType of Stype list
		 | RecordType of (Name.name * Stype) list
		 | DataType of (bool * (Name.name * (Name.name * Stype) list) list) (* bool: true if scalar *)

  datatype Sexp  = S_Con of Name.name 
		 | S_Num of int 
		 | S_App of Sexp list 
		 | S_Upd of Sexp * Sexp * Sexp
		 | S_Lam of (Name.name * Stype) list * Sexp
		 | S_Qnt of string * (Name.name * Stype) list * Sexp
		 | S_Let of (Name.name * Stype * Sexp) list * Sexp
		 | S_MkR of (Name.name * Sexp) list

  (* smart constructors *)
  fun mk_Con s   = S_Con (Name.lift s)
  fun mk_App []  = Util.interfaceError "Internal: mk_App passed an empty list!"
    | mk_App [t] = t
    | mk_App xs  = S_App xs
  fun mk_BasicType s = BasicType (Name.lift s)

  fun arityOf (FuncType ts) = length ts - 1
    | arityOf _             = 0

  fun namesOf (BasicType n)      = [n]
    | namesOf (Uninterpreted n)  = [n]
    | namesOf (FuncType ts)      = Util.concatMap namesOf ts
    | namesOf (TupleType ts)     = Util.concatMap namesOf ts
    | namesOf (RecordType ts)    = Util.concatMap (fn (n, t) => n :: namesOf t) ts
    | namesOf (DataType (_, cs)) = let fun namesOfArgs (n, t) = n :: namesOf t
				       fun namesOfCs (n, lst) = n :: Util.concatMap namesOfArgs lst
				   in Util.concatMap namesOfCs cs
				   end

  val ppName = PPR.str o Name.toString
  val parens = PPR.enclose "(" ")"
  fun block ps = PPR.blk (1, ps)
  fun ppApp []      = parens []
    | ppApp [f]     = parens [f]
    | ppApp (f::fs) = parens [f, PPR.brk 1, PPR.blk (0, PPR.breaks fs)]
  val parens = PPR.enclose "(" ")"
  fun mapB f xs = PPR.breaks (map f xs)
  fun ppVT (n, t) = block [ppName n, PPR.keyword "::", ppType t]
  and ppVTE (n, t, e) = parens [block [ppName n, PPR.keyword "::", ppType t, PPR.brk 1, ppExp e]]
  and ppVE (n, e) = block [ppName n, PPR.keyword "::", ppExp e]
  and ppType stype 
    = let fun shC (n, [])   = ppName n
	    | shC (n, args) = ppApp (ppName n :: map ppVT args)
	  fun shT (BasicType t)     = ppName t
	    | shT (Uninterpreted t) = ppName t
	    | shT (FuncType args)   = ppApp (PPR.keyword "->"       :: map shT args)
	    | shT (TupleType args)  = ppApp (PPR.keyword "tuple"    :: map shT args)
	    | shT (RecordType args) = ppApp (PPR.keyword "record"   :: map ppVT args)
	    | shT (DataType (true,  args)) = ppApp (PPR.keyword "scalar"   :: map shC args)
	    | shT (DataType (false, args)) = ppApp (PPR.keyword "datatype" :: map shC args)
      in shT stype
      end
  and ppExp (S_Con n)            = ppName n
    | ppExp (S_Num i)            = PPR.str (if i < 0 then "-" ^ Int.toString (abs i) else Int.toString i)
    | ppExp (S_App args)         = ppApp (map ppExp args)
    | ppExp (S_MkR args)         = ppApp [PPR.keyword "mk-record", PPR.blk (0, mapB ppVE args)]
    | ppExp (S_Upd (f, p, nv))   = ppApp [PPR.keyword "update", ppExp f, parens [ppExp p], ppExp nv]
    | ppExp (S_Lam (args, e))    = ppApp [PPR.keyword "lambda", parens (mapB ppVT args),    ppExp e]
    | ppExp (S_Qnt (n, args, e)) = ppApp [PPR.keyword n       , parens (mapB ppVT args),    ppExp e]
    | ppExp (S_Let (bndgs, b))   = ppApp [PPR.keyword "let"   , parens (mapB ppVTE bndgs),  ppExp b]

  val showStype = PPR.string_of o ppType
  val showSexp  = PPR.string_of o ppExp

  fun assembleScript printer (setup, tps, defs, hyps, sexp)
    = let val typedefs = map (fn n =>  parens [PPR.keyword "define-type", PPR.brk 1, ppName n])
			     (Library.map_filter (fn (x, mb0) => case mb0 of NONE => SOME x | _ => NONE) tps)
	  val optTyps  = map (fn (n, t) => parens [PPR.keyword "define-type", PPR.brk 1, PPR.blk (0, [ppName n, PPR.brk 1, PPR.blk (0, [ppType t])])])
			     (Library.map_filter (fn (x, mbO) => case mbO of NONE => NONE | _ => SOME (x, the mbO)) tps)
	  val defines  = map (fn (v, t) => parens [PPR.keyword "define", PPR.brk 1, ppName v, PPR.keyword "::", ppType t]) defs
	  fun asrt s   = ppApp [PPR.keyword "assert", s]
	  val hypExprs = map (asrt o ppExp) hyps
	  val sexpr    = asrt (ppExp sexp)
      in ( setup
	 , map printer typedefs
	 , map printer optTyps
	 , map printer defines
	 , map printer hypExprs
	 , printer sexpr) 
      end
	
  fun showScript termStr script
    = let val (setup, types, optTyps, defines, asserts, sexpr) = assembleScript (PPR.plainPrint PPR.string_of) script
	  fun line []  = ";;; none\n"
	    | line xs  = foldr (fn (x, y) => x ^ "\n" ^ y) "" xs
      in   ";;; Automatically generated by the ismt tactic, do not edit!\n" 
         ^ ";;; Generated from the HOL term:\n"
         ^ Library.prefix_lines ";;;     " termStr ^ "\n\n"
	 ^ ";;; Yices set-up\n"
	 ^ line setup
	 ^ "\n;;; Uninterpreted types:\n"
	 ^ line types
	 ^ "\n;;; Type declarations:\n"
         ^ line optTyps
	 ^ "\n;;; Constants:\n"
	 ^ line defines 
	 ^ "\n;;; Hypotheses:\n"
         ^ line asserts
	 ^ "\n;;; Negated goal:\n"
         ^ sexpr
	 ^ "\n\n(check)"
         ^ "\n;;; End of generated Yices file.\n"
      end
end (* IL *)

structure YicesInternals = 
struct
  type Typ = IL.Stype
  type Exp = IL.Sexp 

  val boolT        = IL.mk_BasicType "bool"
  val natT         = IL.mk_BasicType "nat"
  val intT         = IL.mk_BasicType "int"

  val true_const   = IL.mk_Con "true"
  val false_const  = IL.mk_Con "false"
  val plus_const   = IL.mk_Con "+"
  val minus_const  = IL.mk_Con "-"
  val times_const  = IL.mk_Con "*"   
  val divide_const = IL.mk_Con "/"   
  val eq_const     = IL.mk_Con "="   
  val neq_const    = IL.mk_Con "/="  
  val lessEq_const = IL.mk_Con "<="  
  val less_const   = IL.mk_Con "<"   
  val imp_const    = IL.mk_Con "=>"  
  val and_const    = IL.mk_Con "and"
  val or_const     = IL.mk_Con "or"
  val not_const    = IL.mk_Con "not"
  val if_const     = IL.mk_Con "if"
  val pair_const   = IL.mk_Con "mk-tuple"
  val select_const = IL.mk_Con "select"
  val update_const = IL.mk_Con "update"
  val div_const    = IL.mk_Con "div"
  val mod_const    = IL.mk_Con "mod"

  fun isYicesNumericType t = t = natT orelse t = intT

  val basicTypesList = [ (HOLogic.boolT, boolT), (HOLogic.natT, natT) 
                       , (HOLogic.intT, intT),   (Type ("prop", []), boolT)]

  fun holTypeOf t = case List.find (fn (_, y) => y = t) basicTypesList of
			SOME (h, _) => h
		      | NONE => Util.interfaceError ("holTypeOf called on unknown type:" ^ IL.showStype t)

  fun yicesTypeOf t = case List.find (fn (h, _) => h = t) basicTypesList of
			  SOME (_, y) => y
			| NONE => Util.interfaceError ("yicesTypeOf called on unknown type.")

  val yicesReserved = [ "true", "false", "define-type", "define", "subtype", "subrange", "tuple", "record", "datatype"
		      , "scalar", "bitvector", "and", "or", "not", "=>", "=", "/=", "::", "if", "ite", "let"
		      , "forall", "exists", "lambda", "mk-tuple", "select", "mk-record", "update", "mk-bv"
		      , "bv-concat", "bv-extract", "bv-shift-left0", "bv-shift-left1", "bv-shift-right0", "bv-shift-right1"
		      , "bv-sign-extend", "bv-and", "bv-or", "bv-xor", "bv-not", "bv-add", "bv-sub", "bv-mul", "bv-neg"
		      , "bv-lt", "bv-le", "bv-gt", "bv-ge", "bv-slt", "bv-sle", "bv-sgt", "bv-sge"
		      , "bool", "nat", "int", "status", "assert", "assert+", "check", "retract", "check"
		      , "set-evidence!", "set-verbosity!", "set-arith-only!", "push", "pop", "echo", "include", "reset"
		      , "dump-context", "+", "-", "*", "/", "<=", "div", "mod"
		      ]

  fun isReserved nm = member (op =) yicesReserved (Name.toString nm)

  fun unreserve nm = if isReserved nm
		     then unreserve (Name.incrIndex nm)
		     else nm

  (* drop not-not; not-= becomes /=, not-/= becomes =, anything else gets a not in front *)
  fun negate y = case y of
		     IL.S_App (f :: rest) => if f = not_const 
					     then IL.mk_App rest
					     else if f = eq_const
					     then IL.mk_App (neq_const :: rest)
					     else if f = neq_const 
					     then IL.mk_App (eq_const :: rest)
					     else IL.mk_App [not_const, y] 
		   | _                    => if      y = true_const  then false_const
					     else if y = false_const then true_const
					     else 			  IL.mk_App [not_const, y] 

  val yicesSetup = ["(set-evidence! true)"]
end (* YicesInternals *)

structure Isa2Yices =
struct

  val allowMutualRecursion = false (* Yices doesn't support mutual recursion; set this flag
				    * to true to experiment; should be left false normally. *)

  structure Y = YicesInternals

  fun varifyTerm t = #2 (Type.varify_global [] t)

  datatype FieldType = F_Function | F_Selector | F_Updater of Name.name | F_Case of (Name.name * (string * string list) list)

  fun showFieldType F_Function    = "function"
    | showFieldType F_Selector    = "selector"
    | showFieldType (F_Updater n) = "updater (" ^ Name.toString n ^ ")"
    | showFieldType (F_Case _)    = "case-expression"

  fun isFieldFunction ft = case ft of F_Function    => true | _ => false
  fun isFieldSelector ft = case ft of F_Selector    => true | _ => false
  fun isFieldUpdater  ft = case ft of (F_Updater _) => true | _ => false
  fun isFieldCase     ft = case ft of (F_Case _)    => true | _ => false

  val termTab     : ((Term.term * (Y.Exp * int * FieldType)) list) ref = ref [];
  val newTypTab   : (Term.typ * (Name.name * Y.Typ option)) list ref = ref [];
  val defineTab   : ((Name.name * Y.Typ) list) ref = ref [];
  val hypTab      : (Y.Exp list) ref = ref [];
  val recordTab   : (((string * Term.typ) * (string * Term.typ) list * (Y.Exp list -> Y.Exp) * int) list) ref = ref []
  val genSymTab   : (Name.name list) ref = ref []
  val accessorTab : (Term.term list) ref = ref (map varifyTerm
		             [ @{term "Option.the"}
		             , @{term "List.hd"}
			     , @{term "List.tl"}
			     ])
  val topLevel    : bool ref = ref true;

  fun lookupTermTab comp   = List.find comp (!termTab)

  local
      fun addToTab tab entry   = tab := entry :: (!tab)
  in
  fun addToTermTab       (h, (y, a)) = addToTab termTab (h, (y, a, F_Function))  
  fun addToTermTabSel    (h, (y, a)) = addToTab termTab (h, (y, a, F_Selector))   
  fun addToTermTabUpd f  (h, (y, a)) = addToTab termTab (h, (y, a, F_Updater f))
  fun addToTermTabCase d (h, (y, a)) = addToTab termTab (h, (y, a, F_Case d))
  val addToHypTab                    = addToTab hypTab
  val addToDefineTab                 = addToTab defineTab
  val addToNewTypTab                 = addToTab newTypTab
  val addToRecordTab                 = addToTab recordTab
  val addToGenSymTab                 = addToTab genSymTab
  fun addAccessor t                  = addToTab accessorTab (varifyTerm t)
  end

  (* Note that "equality" and "if" has to be treated specifically, due to their truly polymorphic nature,
   * so we cannot just add them to the table and be done! 
   *)
  fun initTermTab () 
    = let fun binOp T = Type ("fun", [T, Type ("fun", [T, T])])
	  fun relOp T = Type ("fun", [T, Type ("fun", [T, HOLogic.boolT])])
      in addToTermTab (HOLogic.true_const,			(Y.true_const,   0));
         addToTermTab (HOLogic.false_const,			(Y.false_const,  0));
	 addToTermTab (Const (@{const_name plus_class.plus},	binOp HOLogic.intT),  (Y.plus_const,   2));
	 addToTermTab (Const (@{const_name plus_class.plus},	binOp HOLogic.natT),  (Y.plus_const,   2));
	 addToTermTab (Const (@{const_name minus_class.minus},	binOp HOLogic.intT),  (Y.minus_const,  2));
	 (* 
	 The following is *not* sound since 2-3=0 for naturals! Yices would do the wrong thing..
	 addToTermTab (Const (@{const_name HOL.minus_class.minus},		binOp HOLogic.natT),  (Y.minus_const,  2)); 
	 *)
	 addToTermTab (Const (@{const_name times_class.times},	binOp HOLogic.intT),  (Y.times_const,  2));
	 addToTermTab (Const (@{const_name times_class.times},	binOp HOLogic.natT),  (Y.times_const,  2));
	 (* don't define divide; Isabelle doesn't define them!
	 addToTermTab (Const (@{const_name HOL.divide},		binOp HOLogic.intT),  (Y.divide_const, 2));
	 addToTermTab (Const (@{const_name HOL.divide},		binOp HOLogic.natT),  (Y.divide_const, 2)); 
	 *)
	 addToTermTab (Const (@{const_name ord_class.less_eq},	relOp HOLogic.intT),  (Y.lessEq_const, 2));
	 addToTermTab (Const (@{const_name ord_class.less_eq},	relOp HOLogic.natT),  (Y.lessEq_const, 2));
	 addToTermTab (Const (@{const_name ord_class.less},	relOp HOLogic.intT),  (Y.less_const,   2));
	 addToTermTab (Const (@{const_name ord_class.less},	relOp HOLogic.natT),  (Y.less_const,   2));
	 addToTermTab (Const (@{const_name HOL.implies},	relOp HOLogic.boolT), (Y.imp_const,    2));
	 addToTermTab (Const (@{const_name HOL.conj},		relOp HOLogic.boolT), (Y.and_const,    2));
	 addToTermTab (Const (@{const_name HOL.disj},		relOp HOLogic.boolT), (Y.or_const,     2))
	 (* div and mod requires special attention since in Isabelle:
	       x mod 0 = x
	       x div 0 = 0
	    which is not the case in Yices
	 addToTermTab (Const (@{const_name Divides.div_class.div},	binOp HOLogic.intT),  (Y.div_const,    2));
	 addToTermTab (Const (@{const_name Divides.div_class.div},	binOp HOLogic.natT),  (Y.div_const,    2));
	 addToTermTab (Const (@{const_name Divides.div_class.mod},	binOp HOLogic.intT),  (Y.mod_const,    2));
	 addToTermTab (Const (@{const_name Divides.div_class.mod},	binOp HOLogic.natT),  (Y.mod_const,    2))
	 *)
      end

  (* These are the numeric types we understand and support. All others will go uninterpreted. *)
  fun isHOLNatType t = t = HOLogic.natT
  fun isHOLIntType t = t = HOLogic.intT
  fun isHOLNumericType t = isHOLNatType t orelse isHOLIntType t

  (* Recognizes HOL records *)
  fun isHOLRecordType t = Record.dest_recTs t <> []
	
  (* expToHOL is only a "poor man"'s version; supposed to convert only those s-expressions
   * that Yices will use in printing it's counter examples! It's not a full-fledged 
   * expression to HOL converter by any means!
   *)
  fun expToHOL uninterpretedConstants s
    = let val unints = ref uninterpretedConstants
	  fun addUnint n ht = 
	      let val mbS = case ht of
				Const (hn,  _) => SOME (Long_Name.base_name hn)
			      | Free  (hn,  _) => SOME (Long_Name.base_name hn)
			      | Var   (hin, _) => SOME (Long_Name.base_name (Library.string_of_indexname hin))
			      | _              => NONE
	      in case mbS of
		     NONE => ()
		   | SOME s => if member (op =) (!unints) s orelse not (member (op =) (map #1 (!defineTab)) n)
			       then () 
			       else unints := s :: (!unints) 
	      end
	  fun bailOut msg = Util.interfaceError ("e2h: " ^ msg ^ ", while processing: " ^ IL.showSexp s)
	  fun mkSMTConst i = @{term "ismt_const"} $ (HOLogic.mk_number HOLogic.intT i)
	  fun getTypeOf ht = fastype_of ht handle _ => Util.interfaceError ("Failed to correctly type: " ^ Syntax.string_of_term_global (!Util.currentTheory) ht) 
	  fun flatten  (Type ("fun", [x, y])) = x :: flatten y
	    | flatten t                       = [t]
	  fun mkRecord args 
	    = let val sep = IL.mk_Con "::"
		  fun collect [] = []
		    | collect (IL.S_Con nm::s::v::r) = if s = sep then ((Name.toString nm, v) :: collect r) 
						       else bailOut "Expected record separator ::, but didn't find one!"
		    | collect _ = bailOut "Expected Yices record constructor syntax, but didn't find one!"
		  val params = collect args
		  val fields = map #1 params
	      in case List.find (fn (_, fts, _, _) => map #1 fts = fields) (!recordTab) of
		     NONE => bailOut ("Cannot find the HOL record with fields: " ^ commas fields)
		   | SOME (c, fts, _, _) => 
		     let val hts = map #2 fts
			 val values = map (Library.uncurry e2h) (ListPair.zip (map #2 params, map SOME hts))
		     in SOME (Library.foldl (op $) (Const c, values @ [Const ("Product_Type.Unity", Type ("Product_Type.unit", []))]))
		     end
	      end
	  and special (IL.S_Con nm) args eT
	      = (case Name.toString nm of
		     "select" =>  (case args of (* could be a tuple or a record *)
				       [t, IL.S_Num i] => if i = 1 then SOME (@{term "fst"} $ e2h t eT)
							  else if i = 2 then SOME (@{term "snd"} $ e2h t eT)
							  else NONE
				     | [t, IL.S_Con n] => SOME (e2h (IL.mk_App [IL.S_Con n, t]) eT)
				     | _ => NONE)
		   | "mk-tuple" => (case args of
					[e1, e2] => let val (t1, t2) = case eT of 
									   SOME (Type ("*", [t1, t2])) => (SOME t1, SOME t2)
									 | _ => (NONE, NONE)
						    in SOME (Library.foldl (op $) (@{term "Pair"}, [e2h e1 t1, e2h e2 t2]))
						    end
				      | _ => NONE)
		   | "mk-record" => mkRecord args 
		   | _           => NONE)
	    | special _ _ _ = NONE
	  and e2h (IL.S_Con n) mbType
	    = (case lookupTermTab (fn (_, (IL.S_Con y, _, _)) => y = n | _ => false) of
		   NONE        => (let fun binOp T = Type ("fun", [T, Type ("fun", [T, T])])
		   		       val t = (case mbType of
				       		  NONE    => HOLogic.intT (* take a guess! *)
						| SOME ht => ht)
		   		   in (case Name.toString n of
		   		         "div" => Const (@{const_name Divides.div_class.div}, binOp t)
				       | "mod" => Const (@{const_name Divides.div_class.mod}, binOp t)
				       | _     => bailOut ("Unknown Yices Name: " ^ Name.toString n))
				   end)
		 | SOME (h, _) => (addUnint n h; h))
	    | e2h (IL.S_Num i) (SOME hT) = if isHOLNumericType hT then HOLogic.mk_number hT i else mkSMTConst i
	    | e2h (IL.S_Num i) NONE      = mkSMTConst i
	    | e2h (IL.S_App []) _   = bailOut "Empty application received"
	    | e2h (IL.S_App (f::fs)) eT
	      = (case special f fs eT of
		     SOME r => r
		   | NONE => let val f' = e2h f NONE
			     in (case getTypeOf f' of
				     Type ("fun", [])  => bailOut ("Empty function type received")
				   | Type ("fun", ats) => let val argTs = Util.butLast (flatten (Type ("fun", ats)))
							      val hargs = map (Library.uncurry e2h) (ListPair.zip (fs, map SOME argTs))
							  in Library.foldl (op $) (f', hargs)
							  end
				   | _                 => bailOut ("Non-function type received"))
			     end)
	    | e2h (IL.S_Upd (tuple, IL.S_Num i, nv)) eT
	      = let val (t1, t2) = case eT of 
				       SOME (Type ("*", [t1, t2])) => (SOME t1, SOME t2)
				     | _ => (NONE, NONE)
		in if i = 1
		   then Library.foldl (op $) (@{term "Pair"}, [e2h nv t1, @{term "snd"} $ e2h tuple eT])
		   else if i = 2
		   then Library.foldl (op $) (@{term "Pair"}, [@{term "fst"} $ e2h tuple eT, e2h nv t2])
		   else bailOut ("Tuple update found with invalid index: " ^ Int.toString i)
		end
	    | e2h (IL.S_Upd (f, IL.S_App [loc], nv)) eT
	      = let val (ta, tr) = case eT of
				       NONE    => (NONE, NONE)
				     | SOME hT => (case flatten hT of []  => (NONE, NONE)
								    | [x] => (SOME x, NONE)
								    | xs  => (SOME (List.hd xs), SOME (List.last xs)))
		in Library.foldl (op $) (@{term "Fun.fun_upd"}, [e2h f eT, e2h loc ta, e2h nv tr])
		end
	    (** Function updates with multiple locations and record updates are not supported! 
	     * | e2h (IL.S_Upd (f, IL.S_App locs, nv)) eT  
	     * | e2h (IL.S_Upd (r, IL.S_Con f, nv)) eT
	     **)
	    | e2h t _ = bailOut ("Unexpected construct " ^ IL.showSexp t)
	  fun dest_equal (IL.S_App [IL.S_Con n, a1, a2]) = if Name.prefixOf n = "=" then SOME (a1, a2) else NONE
	    | dest_equal _ = NONE
          val res = case dest_equal s of
			NONE => e2h s NONE
		      | SOME (a1, a2) => let val a1' = e2h a1 NONE
					     val a2' = e2h a2 (SOME (getTypeOf a1'))
					 in HOLogic.mk_eq (a1', a2')
					 end
      in (res, !unints)
      end

  fun parseSexp s 
    = let fun clean s =
	      let fun cln []                  sofar = List.rev sofar
		    | cln (#":" :: #":" :: r) sofar = cln r (#" " :: #":" :: #":" :: #" " :: sofar)
		    | cln (#"(" :: r)         sofar = cln r (#" " :: #"(" :: #" " :: sofar)
		    | cln (#")" :: r)         sofar = cln r (#" " :: #")" :: #" " :: sofar)
		    | cln (c::r)              sofar = cln r (c::sofar)
	      in String.implode (cln (String.explode s) [])
	      end
	  fun scanWords is_let cs =
	      let fun scan1 [] = []
	            | scan1 cs = let val (lets, rest) = take_prefix is_let cs
		                     in implode lets :: scanWords is_let rest 
				 end
              in scan1 (#2 (take_prefix (not o is_let) cs)) 
	      end
	  val toks = scanWords (not o Symbol.is_blank) (Symbol.explode (clean s))
	  fun perror () = Util.interfaceError ("Cannot understand the Yices response: " ^ s)
	  fun pTok tok = case Int.fromString tok of NONE => IL.S_Con (Name.toName tok) | SOME i => IL.S_Num i
	  fun app [] = Util.interfaceError ("app received an empty list!")
	    | app (toks as (f :: rest))
	      = if f <> Y.update_const 
		then IL.S_App toks
		else case rest of
			 [what, loc, newval] => IL.S_Upd (what, loc, newval)
		       | _                   => IL.S_App toks
	  fun parse []          = perror ()
	    | parse ("("::toks) = let val (f, r) = parseApp toks [] in (app f, r) end
	    | parse (")"::_)    = perror ()
	    | parse [tok]       = (pTok tok, [])
	    | parse _           = perror ()
	  and parseApp []          _     = perror ()
	    | parseApp (")"::toks) sofar = (List.rev sofar, toks)
	    | parseApp ("("::toks) sofar = let val (f, r) = parse ("("::toks) in parseApp r (f :: sofar) end
	    | parseApp (tok::toks) sofar = parseApp toks (pTok tok :: sofar)
      in case parse toks of
	      (sexp, []) => sexp
	    | _          => perror ()
      end


  val specialChars = String.explode "():"

  fun mkUniqueNameWorker shouldAdd env starter =
      let fun underscore s 
	    = let fun cvt c = if Char.isAscii c andalso Char.isPrint c andalso not (Char.isSpace c) andalso not (member (op =) specialChars c)
			      then c else #"_"
		  fun cvtInitial c = let val c' = cvt c in if Char.isDigit c' then [#"_", c'] else [c'] end
	      in String.implode (case String.explode s of
				     []      => [#"_"] (* not really possible *)
				   | [c]     => cvtInitial c
				   | (c::cs) => cvtInitial c @ List.map cvt cs)
	      end		
          val starter' = Name.construct (underscore (Name.prefixOf starter), Name.indexOf starter)
	  val namesInScope =   Util.concatMap (fn (_, (n, mbT)) => case mbT of NONE => [n] | SOME t => IL.namesOf t) (!newTypTab)
			     @ Util.concatMap (fn (n, t) => n :: IL.namesOf t) (!defineTab)
			     @ Util.concatMap (fn (Free (s, _), _) => [Name.lift s] | _ => []) env
			     @ (!genSymTab)
	  val conflicts = Library.sort (fn (n1, n2) => rev_order (Int.compare (Name.indexOf n1, Name.indexOf n2)))
				       (List.filter (fn n => Name.prefixOf n = Name.prefixOf starter') namesInScope)
	  val nm = case conflicts of
		       []     => starter'
		     | (n::_) => Name.incrIndex n
          val res = Y.unreserve nm
      in if shouldAdd then addToGenSymTab res else ();
         res
      end

  fun mkUniqueName _   ""  = Util.interfaceError ("mkUniqueName called with empty prefix")
    | mkUniqueName env pre = mkUniqueNameWorker true env (Name.lift pre)

  local structure D = Datatype and  DA = Datatype_Aux and R = Record
  in
  fun newRecordType env pending (origType as Type (extType, _))
    = let fun bailOut s = Util.interfaceError ("newRecordType: " ^ s ^ " (original type: " ^ Syntax.string_of_typ_global (!Util.currentTheory) origType ^ ")")
	  val hFields = case R.get_extT_fields (!Util.currentTheory) origType of
	                    (fs, (_, Type ("Product_Type.unit", []))) => fs
			  | (_, (n, t)) => bailOut ("Yices does not support extensible records! Detected with extra field spec: " 
						    ^ n ^ " ==> " ^ Syntax.string_of_typ_global (!Util.currentTheory) t)
	  val suffix = 
	      let fun collectFrees (Type (_, ts))        = Util.concatMap collectFrees ts
		    | collectFrees (t as (TFree (_, _))) = [t]
		    | collectFrees (TVar _)              = bailOut "Unexpected type-variable!"
		  val frees = Util.concatMap (collectFrees o #2) hFields
		  val inst = space_implode "-" (map (PPR.plainPrint (Syntax.string_of_typ_global (!Util.currentTheory))) frees)
	      in if inst = "" then inst else "-" ^ inst 
	      end
	  val (yRecName, hConstName, hConstType, hTypes) = 
	      let val rN  = Library.unsuffix R.ext_typeN extType
		  val hTs = map #2 hFields
		  val hT  = Library.foldr (fn (a, b) => Type ("fun", [a, b])) (hTs @ [Type ("Product_Type.unit", [])], origType)
	      in (mkUniqueName env (Long_Name.base_name rN ^ suffix) , rN ^ R.extN, hT, hTs)
	      end
	  val yFields = map (fn (n, t) => (Util.trace (fn () => "Converting HOL record field: " ^ n ^ " : " ^ TermUtils.showTyp t);
					   (mkUniqueName env (Long_Name.base_name n), uninterpretType pending env t))) hFields
	  val yicesRecord = IL.RecordType yFields
	  fun addSelector (h, (yField, _)) 
	    = let val hTrm = varifyTerm (Const h)
	      in Util.trace (fn () => "Adding record selector (" ^ Name.toString yField ^ "): " 
				      ^ Syntax.string_of_term_global (!Util.currentTheory) hTrm ^ " : " ^ Syntax.string_of_typ_global (!Util.currentTheory) (type_of hTrm));
		 addToTermTabSel (hTrm, (IL.S_Con yField, 1))
	      end
	  fun addUpdater ((hn, ht), (yf, _))
            = let val hTrm = Const (hn, ht)
		  val yNm  = mkUniqueName env (Long_Name.base_name hn)
	      in Util.trace (fn () => "Adding record updater (field: " ^ Name.toString yf ^ "): " ^ hn ^ " : " ^ Syntax.string_of_typ_global (!Util.currentTheory) ht);
		 addToTermTabUpd yf (hTrm, (IL.S_Con yNm, 2))
	      end
      in Util.trace (fn () => "newRecordType: Generated: " ^ Name.toString yRecName ^ " ===> " ^ IL.showStype yicesRecord);
	 addToNewTypTab (origType, (yRecName, SOME yicesRecord));
	 ListPair.app addSelector (map (fn (n, t) => (n, Type ("fun", [origType, t]))) hFields, yFields);
	 ListPair.app addUpdater  (map (fn (n, t) => (n ^ "_update", Type ("fun", [Type ("fun", [t, t]), Type ("fun", [origType, origType])]))) hFields, yFields);
	 Util.trace (fn () => "newRecordType: Adding record creator: " ^ hConstName ^ " : " ^ Syntax.string_of_typ_global (!Util.currentTheory) hConstType);
	 addToRecordTab ((hConstName, hConstType)
		       , (ListPair.zip (map (Name.toString o #1) yFields, hTypes))
		       , fn vals => IL.S_MkR (ListPair.zip (map #1 yFields, vals))
		       , length hFields); 
	 IL.BasicType yRecName
      end
    | newRecordType _ _ origType = Util.interfaceError ("newRecordType: unexpected type: " ^ TermUtils.showTyp origType)
  and newDataType env pending (origType as Type (hTyNm, Ts))
    = (case AList.lookup (op =) pending origType of
	   SOME t => (Util.trace (fn () => "newDataType: recursive instance at " ^ Syntax.string_of_typ_global (!Util.currentTheory) origType ^ " found, stopping generation.");
		      t)
	 | NONE => 
	   let val _ = Util.trace (fn () => "newDataType: working on: " ^ TermUtils.showTyp origType)
	       fun bailOut s = Util.interfaceError ("newDataType: " ^ s ^ " (original type: " ^ Syntax.string_of_typ_global (!Util.currentTheory) origType ^ ")")
	       (* check and reject mutual recursion if not allowed *)
	       val caseName = let val {descr, sorts, case_name, ...} = D.the_info (!Util.currentTheory) hTyNm
			      in if not allowMutualRecursion 
				 then let val recTypes = DA.get_rec_types descr sorts
				      in if length recTypes > 1 then
					     Util.interfaceError ("Yices does not support mutually recursive types, detected amongst: " ^
								  (Library.space_implode " and " (map (Syntax.string_of_typ_global (!Util.currentTheory)) recTypes)))
					 else 
					     case_name
				      end
				 else case_name
			      end
	       val suffix = let val inst = space_implode "-" (map (PPR.plainPrint (Syntax.string_of_typ_global (!Util.currentTheory))) Ts) in if inst = "" then inst else "-" ^ inst end
	       val dtName  = mkUniqueName env (Long_Name.base_name hTyNm ^ suffix) 
	       val constrs = 
		   let val (tvs, constrDecls) = (D.the_spec (!Util.currentTheory) hTyNm)
		       val constrTyps = the (D.get_constrs (!Util.currentTheory) hTyNm)
		       val tvmapping = let fun walk [] []                 = []
					     | walk (f::r1) (TFree t::r2) = if f = t then walk r1 r2 else (f, TFree t) :: walk r1 r2
					     | walk (_::_) (TVar _::_)    = bailOut ("Ts not containing TVar's assumption failing!")
					     | walk (f::r1) (t::r2)       = (f, t) :: walk r1 r2
					     | walk _  _                  = bailOut ("tvmapping equal-length assumption failing!")
				       in walk tvs Ts
				       end
		       fun subst (Type (s, Ts))     = Type (s, map subst Ts)
			 | subst (TFree s)          = (case AList.lookup (op =) tvmapping s of
							   SOME s' => s'
							 | NONE    => TFree s)
			 | subst (TVar ((n, 0), s)) = subst (TFree (n, s))
			 | subst t                  = bailOut ("Unexpected non-zero schematic variable: " ^ TermUtils.showTyp t)
		       val _ = if length constrTyps <> length constrDecls then bailOut ("|types| = |decls| assumption failing") else ()
		       fun monomorphise [] []                       = []
			 | monomorphise ((s, t)::r1) ((s', tl)::r2) = if s <> s' then bailOut ("Constructor name match assumption failing! (Need to sort!)")
								      else (s, subst t, map subst tl) :: monomorphise r1 r2
			 | monomorphise _ _                         = bailOut ("monomorphise equal-length assumption failing!")
		   in monomorphise constrTyps constrDecls
		   end
               (* val _ = Util.trace (fn () => "constructors: " 
					       ^ Util.stringyMap (fn (s, t, ts) => s ^ "\n" ^ TermUtils.showTyp t ^ "\n" ^ Util.stringyMap TermUtils.showTyp ts) 
								 constrs); *)
	       fun mkField ctr tot (t, i) 
		 = let fun stt hT = Syntax.string_of_term_global (!Util.currentTheory) hT ^ " :: " ^ Syntax.string_of_typ_global (!Util.currentTheory) (type_of hT)
		       val hType = Type ("fun", [origType, t])
		       val a_type = uninterpretType ((origType, IL.BasicType dtName) :: pending) env t
		       val (hT, a_name) = case List.find (fn t => Sign.typ_instance (!Util.currentTheory) (hType, type_of t)) (!accessorTab) of
					      NONE => let val a_name = mkUniqueName env ("a" ^ ctr ^ (if tot > 1 then Int.toString i else ""))
							  val hTerm = Const (Name.toString a_name, hType)
						      in warning ("Adding HOL accessor: " ^ stt hTerm);
							 (hTerm, a_name)
						      end
					    | SOME hTerm => 
					      let val basis = (case hTerm of
								   Const (s, _) => Long_Name.base_name s
								 | _            => "a" ^ ctr ^ (if tot > 1 then Int.toString i else ""))
						  val a_name = mkUniqueName env basis
						  val hT = (case hTerm of
						                Const (s, _) => Const (s, hType)
							      | _ => hTerm)
					      in Util.trace (fn () => "Found an accessor: " ^ stt hTerm ^ "; for type: " ^ Syntax.string_of_typ_global (!Util.currentTheory) hType);
						 (hT, a_name)
					      end
		   in  addToTermTab (hT, (IL.S_Con a_name, 1)); (* accessors always have arity 1, right? *)
		       (a_name, a_type)
		   end
	       fun mkConstr (s, t, tl) 
		 = let val c_name = mkUniqueName env (Long_Name.base_name s ^ suffix)
		       val noOfTs = length tl
		       val hTrm = Const (s, t)
		   in Util.trace (fn () => "Constr: " ^ Syntax.string_of_term_global (!Util.currentTheory) hTrm 
					   ^ " with name: " ^ Name.toString c_name ^ " arity: " ^ Int.toString (length tl));
		      addToTermTab (hTrm, (IL.S_Con c_name, length tl)); 
		      (c_name, ListPair.map (mkField (Name.toString c_name) noOfTs) (tl, 1 upto noOfTs))
		   end
               val constructors = map mkConstr constrs
	       fun isScalar (_, fields) = null fields
	       val yicesDT  = IL.DataType (List.all isScalar constructors, constructors)
	       fun addCaseFun d 
		   = let val yCase = mkUniqueName env (Long_Name.base_name caseName)
			 val hTyp = Term.dummyT; (* REVISIT: we will not have a use for this but we might need a better representation here. *)
			 val hTrm = Const (caseName, hTyp)
		     in Util.trace (fn () => "Adding case-analyser: " ^ Name.toString yCase ^ " for " ^ Name.toString dtName ^ ": " ^ caseName);
			addToTermTabCase (dtName, d) (hTrm, (IL.S_Con yCase, 1 + length constructors))
		     end
	   in Util.trace (fn () => "newDataType: Generated: " ^ Name.toString dtName ^ " ===> " ^ IL.showStype yicesDT);
	      addToNewTypTab (origType, (dtName, SOME yicesDT));
	      addCaseFun (map (fn (c, al) => (Name.toString c ^ "?", map (Name.toString o #1) al)) constructors);
	      IL.BasicType dtName
	   end)
	| newDataType _ _ origType = Util.interfaceError ("newDataType: unexpected type: " ^ TermUtils.showTyp origType)
  and uninterpretType pending env typH
    = let fun isDataType s = Option.isSome (D.get_info (!Util.currentTheory) s)
	  fun newtype s = let val nt = mkUniqueName env s
			  in addToNewTypTab (typH, (nt, NONE));
			     IL.Uninterpreted nt
			  end
	  fun unint (TVar ((s, _), _))    = newtype s
	    | unint (TFree (s, _))        = newtype s
	    | unint (Type ("fun", ts))    = IL.FuncType (map (uninterpretType pending env) ts)
	    | unint (Type (@{type_name Product_Type.prod}, ts))
	    				  = IL.TupleType (map (uninterpretType pending env) ts)
	    | unint (ty as (Type (s, _))) = if isDataType s
					    then newDataType env pending ty 
					    else if isHOLRecordType ty
					    then newRecordType env pending ty
					    else (Util.trace (fn () => "Uninterpreting type: " ^ TermUtils.showTyp ty); newtype s)
      in case AList.lookup (op =) Y.basicTypesList typH of
	     SOME typY => typY
	   | NONE      => (case AList.lookup (op =) (!newTypTab) typH of
			       SOME (typY, _)  => IL.Uninterpreted typY
			     | NONE => unint typH)
      end
  end

  fun findBinding env trm 
    = let fun findSelectorUpdater s = Option.map (#2) (lookupTermTab 
							   (fn (Const (n, _), (_, _, ft)) => (n = s andalso (isFieldSelector ft orelse isFieldUpdater ft)) | _ => false))
	  fun checkMatch nm = Option.isSome (List.find (fn (_, (nm', SOME _)) => nm = nm' | _ => false) (!newTypTab))
	  fun findCase s = 
	      case uninterpretType [] env (type_of trm) of
		  IL.FuncType _ => Option.map (#2) (lookupTermTab
							      (fn (Const (n, _), (_, _, (F_Case (nm, _)))) => (n = s andalso checkMatch nm) | _ => false))
		| _ => NONE
      in case List.find (fn (ht, _) => ht = trm) env of (* first look in env *)
             SOME (_, (y, a)) => SOME (y, a, F_Function)
	   | NONE => (case lookupTermTab (fn (ht, _) => ht = trm) of (* exact match in term tab; i.e., with type *)
			SOME (_, y) => SOME y
		      | NONE        => (* a second look, this time for the case of selectors/updaters. *)
				      (case trm of
					   (Const (s, _)) =>(case findSelectorUpdater s of
								  SOME y => SOME y
								| NONE => findCase s)
					 | _ => NONE))
      end

  fun handleAbstraction env (x, xT, b)
    = let fun getUniqueTrans n = let val d = mkUniqueNameWorker false env n
				     val tmpName = Name.toString d
				     val (tmpName', b') = Syntax.variant_abs (tmpName, xT, b)
				 in if tmpName <> tmpName'
				    then (Util.trace (fn () => "getUniqueTrans: recursing since: " ^ tmpName ^ " <> " ^ tmpName');
					  getUniqueTrans (Name.incrIndex n))
				    else (d, tmpName, b')
				 end
	  val (d, tmpName, b') = getUniqueTrans (Name.lift (if x = "_" then "dummy" else x))
	  val dT = uninterpretType [] env xT
	  val envBinding = (Free (tmpName, xT), (IL.S_Con d, IL.arityOf dT))
      in (envBinding, (d, dT), b')
      end

   fun isa2yices trm
    = let fun bailOut s = Util.interfaceError (s ^ " (original term: " ^ Syntax.string_of_term_global (!Util.currentTheory) trm ^ ")")
	  fun flatten (t1 $ t2) = flatten t1 @ [t2]
	    | flatten t         = [t]
	  fun recordSwap (s :: r :: rest) = Y.select_const :: r :: s :: rest
	    | recordSwap _ = bailOut "recordSwap received insufficient no of args!"
	  fun updateSwap field (_ :: func :: r :: rest) 
	       = Y.update_const :: r :: IL.S_Con field :: IL.mk_App [func, IL.mk_App [Y.select_const, r, IL.S_Con field]] :: rest
	    | updateSwap _ _ = bailOut "updateSwap received insufficient no of args!"
	  fun mkIf t tb fb = IL.mk_App [Y.if_const, t, tb, fb]
	  fun mkIsEq (IL.S_Num i) (IL.S_Num j)  = if i = j then Y.true_const else Y.false_const
	    | mkIsEq a            b             = IL.mk_App [Y.eq_const, a, b]
	  fun mkIsNeq (IL.S_Num i) (IL.S_Num j) = if i <> j then Y.true_const else Y.false_const
	    | mkIsNeq a            b            = IL.mk_App [Y.neq_const, a, b]
	  fun mkAnd a b = if      a = Y.true_const  then b 
			  else if b = Y.true_const  then a 
			  else if a = Y.false_const then Y.false_const
			  else if b = Y.false_const then Y.false_const
			  else				 IL.mk_App [Y.and_const, a, b]
	  fun mkOr a b  = if      a = Y.false_const then b 
			  else if b = Y.false_const then a 
			  else if a = Y.true_const  then Y.true_const
			  else if b = Y.true_const  then Y.true_const
			  else				 IL.mk_App [Y.or_const, a, b]
	  fun cvtAbstraction env body
	    = let val (envBinding, binder, b) = handleAbstraction env body
		  val b' = cvt (envBinding :: env) b
	      in (binder, b')
	      end
	  and casify _   _          []  = bailOut "Casify received an empty list of args! impossible!"
	    | casify env (dType, d) (_::args)
	      = let val (params, value) = let val noOfArgs   = length args
					      val noOfDiscrs = length d
					  in if noOfArgs <> noOfDiscrs + 1
					     then bailOut ("Casify: expected " ^ Int.toString (noOfDiscrs + 1) ^ " args, but got: " ^ Int.toString noOfArgs)
					     else Library.split_last args
					  end
		    val (letNeeded, tmpVal) = case value of
						  IL.S_Con _ => (false, value)
						| IL.S_Num _ => (false, value)
						| _          => (true, IL.S_Con (mkUniqueName env "casev"))
		    fun apply ss = map (fn s => IL.mk_App [IL.mk_Con s, tmpVal]) ss
		    fun analyze ss v = Library.foldl (fn (a, b) => IL.mk_App [a, b]) (v, apply ss)
		    fun weave []             = bailOut ("weave: impossible happened, received an empty list")
		      | weave [(v, (_, ss))] = analyze ss v
		      | weave ((v, (r, ss))::rest) = mkIf (IL.mk_App [IL.mk_Con r, tmpVal]) (analyze ss v) (weave rest)
		    val trans = weave (ListPair.zipEq (params, d))
	      in
		    if letNeeded 
		    then let val tmpVar = case tmpVal of
					      IL.S_Con v => v
					    | _ => bailOut ("Casify: impossible happened; let expression created without a constant!")
			 in [IL.S_Let ([(tmpVar, IL.BasicType dType, value)], trans)]
			 end
		    else [trans]
	      end
          and eta_expand alwaysExpand trans args env typH present more
	      = let fun eta ()
		      = let val typY = uninterpretType [] env typH
			    fun flatten []               = []
			      | flatten [IL.FuncType xs] = flatten xs
			      | flatten (t::r)           = t :: flatten r
                        in case typY of
	                     IL.FuncType xs => let val allTs = flatten xs
						   val needTs = List.take (List.drop (allTs, present), more)
		                                   val needVs = map (fn t => (mkUniqueName env "etav", t)) needTs
                                               in IL.S_Lam (needVs, trans (args @ map (IL.S_Con o #1) needVs))
				               end
		            | _ => bailOut ("eta_expand: expected function type but found: " ^ IL.showStype typY)
                        end
                in case (args, present) of
		     (IL.S_Con nm :: _, 0) => if alwaysExpand orelse Y.isReserved nm  
		                              then eta () 
					      else IL.mk_App args 
		   | _ => eta ()
                end
          and lookUpConversion env trm args
	    = case findBinding env trm of
		  SOME (y, reqCnt, fieldType) => 
		  let val givenCnt = length args
		      (* do not require saturation for functions, but eta-expand if not given enough! *)
		      val curCount = if givenCnt > reqCnt then reqCnt else givenCnt (* take minimum *)
		      val (curArgs, remainingArgs) = Util.splitAt curCount args
		      val params = y :: map (cvt env) curArgs
		      val app' = case fieldType of
				     F_Function      => params
				   | F_Selector      => recordSwap params
				   | F_Updater field => updateSwap field params
				   | F_Case d        => casify env d params
		      (* eta-expand if necessary *)
		      val app = if curCount < reqCnt 
		                then eta_expand false IL.mk_App app' env (type_of trm) curCount (reqCnt - curCount)
				else IL.mk_App app'
		  in SOME (app, remainingArgs)
		  end
		| NONE => (case trm of
			       Const (n, _) => (case List.find (fn ((s, _), _, _, _) => s = n) (!recordTab) of
						    SOME (_, _, yf, reqCnt) => 
						    let val givenCnt = length args
						    in (* require saturation for record constructors *)
						       if reqCnt > givenCnt
						       then bailOut ("Record constructor: " ^ n ^ " requires " ^ Int.toString reqCnt ^
								     " arguments, but here given only " ^ Int.toString givenCnt)
						       else let val (curArgs, remainingArgs) = Util.splitAt reqCnt args
							    in case remainingArgs of
								   (Const ("Product_Type.Unity", Type ("Product_Type.unit", [])) ::ts) 
								   => SOME (yf (map (cvt env) curArgs), ts)
								 | ts => bailOut ("Cannot locate the expected unit argument in record construction!" 
										  ^ Util.stringyMap TermUtils.showTerm ts)
							    end
						    end
						  | NONE => NONE)
			     | _ => NONE)
	  and uninterpret _   [] = Util.interfaceError ("uninterpret called with an empty list!")
	    | uninterpret env (t::args) =
	        (case lookUpConversion env t args of
		     SOME r => r
		   | NONE => let val typH = type_of t
				 val typY = uninterpretType [] env typH
			     in (* uninterpreting might have made this term available *)
				case lookUpConversion env t args of 
                                    SOME r => r
				  | NONE => (* give up and uninterpret *)
				     let val _ = if true (* set to true for shorter debug *)
						 then Util.trace (fn () => "Uninterpreting term: " 
									   ^ Syntax.string_of_term_global (!Util.currentTheory) t ^ " :: " 
									   ^ Syntax.string_of_typ_global (!Util.currentTheory) typH)
						 else Util.trace (fn () => "Uninterpreting term: " ^ TermUtils.showTerm t)
			                 val nm  = mkUniqueName env (case t of Const (s, _) => s | Free (s, _)  => s | _ => "v")
					 val trmY = IL.S_Con nm
				     in addToTermTab (t, (trmY, IL.arityOf typY));
					addToDefineTab (nm, typY);
					(* call interpret back so that application is taken care of properly *)
					case interpret env t args of
					    SOME r => r
					  | NONE   => (* this cannot happen! *) 
					              Util.interfaceError ("interpret failed on newly added term!")
				     end
			     end)
	  and translate _ (@{const_name Int.number_of}, Type ("fun", [_, T])) (n::args)
	    = let val num  = HOLogic.dest_numeral n
	    	  val num0 = if num < 0 then 0 else num
	      in if isHOLIntType T
	         then SOME(IL.S_Num num, args)
		 else if isHOLNatType T
		      then SOME (IL.S_Num num0, args) else NONE
	      end
	    | translate env (holName, holT) args
	    = let fun bailOut s = Util.interfaceError ("translate: Internal error: " ^ s ^ " called with incorrect no of or type of args")
		  fun fn0 n f xs  = (case xs of []        => f           | _ =>  bailOut n)
		  fun fn1 n f xs  = (case xs of [a      ] => f a         | _ =>  bailOut n)
		  fun fn2 n f xs  = (case xs of [a, b   ] => f (a, b)    | _ =>  bailOut n)
		  fun fn3 n f xs  = (case xs of [a, b, c] => f (a, b, c) | _ =>  bailOut n)
		  fun mkEntry0 (name, ttest, func) = (name, 0, ttest, fn0 name func)
		  fun mkEntry1 (name, ttest, func) = (name, 1, ttest, fn1 name func)
		  fun mkEntry2 (name, ttest, func) = (name, 2, ttest, fn2 name func)
		  fun mkEntry3 (name, ttest, func) = (name, 3, ttest, fn3 name func)
		  fun funDRT fd fr (Type ("fun", [TD, TR])) = fd TD andalso fr TR
		    | funDRT _   _  _                       = false
		  fun funDT f = funDRT f (K true)
		  fun FST t = IL.mk_App [Y.select_const, t, IL.S_Num 1]
		  fun SND t = IL.mk_App [Y.select_const, t, IL.S_Num 2]
		  fun PAIR (a, b) = IL.mk_App [Y.pair_const, a, b]
		  fun letConverter (a, IL.S_Lam ([(d, dT)], body)) = IL.S_Let ([(d, dT, a)], body)
		    | letConverter (t, a)                          = bailOut ("letConverter, failed with args: " ^ IL.showSexp t ^ ", " ^ IL.showSexp a)
		  fun uminusConverterInt (IL.S_Num i) = IL.S_Num (~i)
		    | uminusConverterInt a            = IL.mk_App [Y.minus_const, IL.S_Num 0, a]
		  fun natMinusConverter (a, b) = let val tmpVar = mkUniqueName env "natMinusV"
		  				     val subtract = IL.mk_App [Y.minus_const, a, b]
						     val comp = IL.mk_App [Y.less_const, IL.S_Con tmpVar, IL.S_Num 0]
		  				 in IL.S_Let ( [(tmpVar, IL.mk_BasicType "int", subtract)]
						             , mkIf comp (IL.S_Num 0) (IL.S_Con tmpVar) )
						 end
		  fun splitConverter a = case holT of
					     (Type ("fun", [Type ("fun", [t1, Type ("fun", [t2, _])]), _])) =>
				             let val tempV = mkUniqueName env "splitv"
						 val tempT = Type ("*", [t1, t2])
						 val first = FST (IL.S_Con tempV)
						 val second = SND (IL.S_Con tempV)
					     in IL.S_Lam ([(tempV, uninterpretType [] env tempT)], IL.mk_App [IL.mk_App [a, first], second])
					     end
					   |  _ => bailOut ("splitConverter: unexpected type: " ^ TermUtils.showTyp holT)
		  fun natCaseConverter (zc, sc, v) 
		    = let val eqZero = IL.mk_App [Y.eq_const, v, IL.S_Num 0]
			  val predv = case v of
					  IL.S_Num 0 => IL.mk_App [Y.minus_const, v, IL.S_Num 1]
					| IL.S_Num n => IL.S_Num (n-1)
					| _          => IL.mk_App [Y.minus_const, v, IL.S_Num 1]
		      in mkIf eqZero zc (IL.mk_App [sc, predv])
		      end
		  fun qntConverter nm (IL.S_Lam (bdg, body)) = IL.S_Qnt (nm, bdg, body)
		    | qntConverter nm a = let val tempV = mkUniqueName env "etav"
					      val tempT = case holT of
							      Type ("fun", [Type ("fun", [t, _]), _]) => uninterpretType [] env t
							    | _ => bailOut "qntConverter: All/Ex expression with unexpected type!"
					  in IL.S_Qnt (nm, [(tempV, tempT)], IL.mk_App [a, IL.S_Con tempV])
					  end
		  fun absConverter a = let val comp = IL.mk_App [Y.less_const, a, IL.S_Num 0]
				       in mkIf comp (IL.mk_App [Y.minus_const, IL.S_Num 0, a]) a
				       end
		  fun natConverter a = let val comp = IL.mk_App [Y.less_const, a, IL.S_Num 0]
		  		       in mkIf comp (IL.S_Num 0) a
				       end
		  fun intConverter a = a  (* No need to do anything in Yices to view a nat as an int *)
		  fun modConverter (a, IL.S_Num 0)        = a
		    | modConverter (a, b as (IL.S_Num _)) = IL.mk_App [Y.mod_const, a, b]
		    | modConverter (a, b) = mkIf (IL.mk_App [Y.eq_const, b, IL.S_Num 0]) a (IL.mk_App [Y.mod_const, a, b])
		  fun divConverter (_, IL.S_Num 0)        = IL.S_Num 0
		    | divConverter (a, b as (IL.S_Num _)) = IL.mk_App [Y.div_const, a, b]
		    | divConverter (a, b) = mkIf (IL.mk_App [Y.eq_const, b, IL.S_Num 0]) (IL.S_Num 0) (IL.mk_App [Y.div_const, a, b])
		  val mappings = [          (* Basics *)
				   mkEntry2 (@{const_name HOL.eq},		K true, fn (a, b) => IL.mk_App [Y.eq_const, a, b])
			         , mkEntry3 (@{const_name HOL.If},		K true, fn (t, tb, fb) => mkIf t tb fb)
			         , mkEntry1 (@{const_name Product_Type.fst},	K true, FST)
			         , mkEntry1 (@{const_name Product_Type.snd},	K true, SND)
				 , mkEntry2 (@{const_name HOL.Let},		K true, letConverter)
				 , mkEntry1 (@{const_name HOL.Not},		K true, Y.negate)
				 , mkEntry2 (@{const_name Product_Type.Pair},	K true, PAIR)
				 , mkEntry3 (@{const_name Fun.fun_upd},		K true, IL.S_Upd)
					    (* Case analysers *)
				 , mkEntry2 (@{const_name Product_Type.prod.prod_case},	K true, fn (f, tup) => IL.mk_App [IL.mk_App [f, FST tup], SND tup])
				 , mkEntry3 (@{const_name Product_Type.bool.bool_case},	K true, fn (tc, fc, v) => mkIf v tc fc)
				 , mkEntry1 (@{const_name prod_case},			K true, splitConverter)
				 , mkEntry3 (@{const_name Nat.nat.nat_case},		K true, natCaseConverter)
					    (* Arithmetic *)
				 , mkEntry0 (@{const_name zero_class.zero},	isHOLNumericType, IL.S_Num 0)
				 , mkEntry0 (@{const_name one_class.one},	isHOLNumericType, IL.S_Num 1)
				 , mkEntry2 (@{const_name minus_class.minus},   funDRT isHOLNatType (funDRT isHOLNatType isHOLNatType), natMinusConverter)
				 						
				 , mkEntry1 (@{const_name uminus_class.uminus}, funDRT isHOLIntType isHOLIntType, uminusConverterInt)
				 (* only support abs at the int type; Isabelle doesn't define the nat instance *)
				 , mkEntry1 (@{const_name abs_class.abs},       funDT isHOLIntType, absConverter)
				 , mkEntry1 (@{const_name Int.nat},		funDRT isHOLIntType isHOLNatType, natConverter)
				 , mkEntry1 (@{const_name Nat.of_nat},		funDRT isHOLNatType isHOLIntType, intConverter)
			         , mkEntry1 (@{const_name Nat.Suc},		funDT (fn t => t = HOLogic.natT), fn a => IL.mk_App [Y.plus_const, a, IL.S_Num 1]) 
				 , mkEntry2 (@{const_name Orderings.ord_class.max},	funDT isHOLNumericType, fn (a, b) => mkIf (IL.mk_App [Y.lessEq_const, a, b]) b a)
				 , mkEntry2 (@{const_name Orderings.ord_class.min},	funDT isHOLNumericType, fn (a, b) => mkIf (IL.mk_App [Y.lessEq_const, a, b]) a b) 
				 	(* 0 dvd 0 is True in Isabelle! 
					   The translation is:
					     a dvd b <-> (a == 0 /\ b == 0) \/ (a /= 0 /\ b `mod` a == 0)
					*)
				 , mkEntry2 (@{const_name dvd_class.dvd},	funDT isHOLNumericType, 
				      fn (a, b) => let val aZero    = mkIsEq (IL.S_Num 0) a
				      		       val bZero    = mkIsEq (IL.S_Num 0) b
						       val bothZero = mkAnd  aZero bZero
						       val aNotZero = mkIsNeq (IL.S_Num 0) a
						       val modVal   = IL.mk_App [Y.mod_const, b, a]
						       val okValue  = mkIsEq (IL.S_Num 0) modVal
				      		   in mkOr bothZero (mkAnd aNotZero okValue)
						   end)
				 	(* div and mod. Requires special attention since in Isabelle:
						x mod 0 = x
						x div 0 = 0
					 *)
				 , mkEntry2 (@{const_name Divides.div_class.mod}, funDRT isHOLIntType (funDRT isHOLIntType isHOLIntType), modConverter)
				 , mkEntry2 (@{const_name Divides.div_class.div}, funDRT isHOLIntType (funDRT isHOLIntType isHOLIntType), divConverter)
				 , mkEntry2 (@{const_name Divides.div_class.mod}, funDRT isHOLNatType (funDRT isHOLNatType isHOLNatType), modConverter)
				 , mkEntry2 (@{const_name Divides.div_class.div}, funDRT isHOLNatType (funDRT isHOLNatType isHOLNatType), divConverter)
					    (* Quantifiers *)
				 , mkEntry1 (@{const_name HOL.All}, K true, qntConverter "forall")
				 , mkEntry1 ("all", 		    K true, qntConverter "forall")
				 , mkEntry1 (@{const_name HOL.Ex},  K true, qntConverter "exists")
				 ] 
	      in case List.find (fn (n, _, ttest, _) => holName = n andalso ttest holT) mappings of
		     NONE => NONE
		   | SOME (_, reqCnt, _, translator)
		     => let val givenCnt = length args
			    val curCount = if givenCnt > reqCnt then reqCnt else givenCnt 
			    val (curArgs, remainingArgs) = Util.splitAt curCount args
			    val params = map (cvt env) curArgs
			    val res = if curCount < reqCnt 
				      then eta_expand true translator params env holT curCount (reqCnt - curCount)
				      else translator params
			in SOME (res, remainingArgs)
			end
	      end
	  and interpret env (trm as (Const (n, holT))) args
	      = (Util.trace (fn () => "Trying to interpret: " ^ Syntax.string_of_term_global (!Util.currentTheory) trm ^ " (#: " ^ Int.toString (length args) ^ ")");
		 case lookUpConversion env trm args of
		     SOME r => SOME r
		   | NONE   => translate env (n, holT) args)
	    | interpret env f args = lookUpConversion env f args 
	  and uninterpretConst env t 
	    = let val (r, args) = uninterpret env [t] 
	      in if null args then r else Util.interfaceError ("uninterpretConst got extra arguments as results!")
	      end
	  and (* Meta-constants *)
	      CVT env (Const (@{const_name HOL.Trueprop}, _) $ p) = cvt env p
	    | CVT env (Const ("Goal",     _) $ p) = cvt env p
	    | CVT env (Const ("==>", _) $ p $ q) = 
	       if !topLevel
	       then let val _ = Util.trace (fn () => "Processing top-level assumption!")
	                val _ = topLevel := false
	                val _ = addToHypTab (cvt env p)
		        val _ = topLevel := true
		    in cvt env q
		    end
               else let val _ = Util.trace (fn () => "Processing inner-level assumption!")
	                fun relOp T = Type ("fun", [T, Type ("fun", [T, T])])
	            in CVT env (Const (@{const_name HOL.implies}, relOp HOLogic.boolT) $ p $ q)
		    end
	      (* Variables, free or otherwise *)
	    | CVT env (t as (Free _))  = uninterpretConst env t
	    | CVT env (t as (Var _))   = uninterpretConst env t
	    | CVT _   (     (Bound _)) = bailOut ("Reference to Bound variable.. Unsupported binding construct (?)")
              (* Abstractions *)
	    | CVT env (Abs b) = 
	      let val (bdg, b') = cvtAbstraction env b 
	      in IL.S_Lam ([bdg], b')
	      end
	    (* Applications *)
	    | CVT env t
	      = (case flatten t of
		     []        => bailOut "Impossible happened, empty application."
		   | (f::args) => let val (f', args') = case interpret env f args of
		                                            SOME r => r
							  | NONE   => uninterpret env (f::args)
		                  in Library.foldl (fn (a, b) => IL.mk_App [a, b]) (f', map (cvt env) args')
				  end)
         and cvt env t = (Util.trace (fn () => "Converting: " ^ (* TermUtils.showTerm t *) Syntax.string_of_term_global (!Util.currentTheory) t); CVT env t)
	 fun strip_top_bounds (t as (Const (s, _) $ Abs (body as (x, _, _))))
	   =  if s = @{const_name HOL.All} orelse s = "all"
	      then
	          let val (envBinding, (d', dT), b) = handleAbstraction [] body
	          in Util.trace (fn () => "Added top-level bound variable: " ^ x ^ " with name: " ^ Name.toString d');
		     addToTermTab envBinding;
		     addToDefineTab (d', dT);
		     strip_top_bounds b
	          end
              else t
	   | strip_top_bounds (Const ("HOL.Trueprop", _) $ t) = strip_top_bounds t
	   | strip_top_bounds (Const ("Goal", _) $ t)     = strip_top_bounds t
	   | strip_top_bounds t = t
      in termTab    := [];
	 defineTab  := [];
         hypTab     := [];
	 newTypTab  := [];
	 recordTab  := [];
	 genSymTab  := [];
         topLevel   := true;
	 initTermTab ();
	 let val trm' = strip_top_bounds trm
	     val neg_prop = Y.negate (cvt [] trm')
	     val script   = ( Y.yicesSetup
			    , List.rev (map #2 (!newTypTab))
			    , List.rev (!defineTab)
			    , List.rev (!hypTab)
			    , neg_prop)
	     val trmS     = (PPR.plainPrint o Syntax.string_of_term_global) (!Util.currentTheory) trm
	 in Util.dumpScript (IL.showScript trmS script);
	    script
	 end
      end
end (* Isa2Yices *)

structure Yices : ISMTBackend_SIG =
struct
  structure Y = YicesInternals

  type Script =   string list                      (* Yices specific set-up *)
		* (Name.name * Y.Typ option) list  (* uninterpreted types + option types *)
                * (Name.name * Y.Typ) list         (* constants *)
		* Y.Exp list                       (* hypotheses *)
		* Y.Exp                            (* final negated assertion *)
  type Model = (string * Y.Exp * Term.term) list * string list (* (yices response * s-exp * corresponding term) list * uninterpreted-constants list *)
  type Options = Context.theory * string option * bool * bool
  val identifier = "Yices"
  fun init args = Util.initGlobals args
	  
  val fromIsabelle = Isa2Yices.isa2yices
  val addAccessor  = Isa2Yices.addAccessor

  fun explainModel ([], _) = ("(No explicit model returned from Yices.)", "(None)")
    | explainModel (model, unintConsts)
      = let fun consts [] = "(None)"
	      | consts ss = commas ss
	in (Library.space_implode "\n" (map (PPR.plainPrint (Syntax.string_of_term_global (!Util.currentTheory)) o #3) model),
            consts unintConsts)
	end
		
  fun decide script 
     = let val (setup, types, defines, optTypes, asserts, sexpr) = IL.assembleScript (PPR.plainPrint PPR.string_of) script
	   val opts  = if !Util.shouldTypeCheck then "-tc" else ""
	   val _     = Util.trace (fn () => "Options passed to Yices are: " ^ opts)
	   val _     = Util.interfaceMessage "Results of Yices run:"
	   fun modelify consts [] = ([], List.rev consts)
	     | modelify consts (s::ss) = let val e = (Isa2Yices.parseSexp s handle _ => IL.mk_Con "CannotTranslate")
				             val (h, consts')     = (Isa2Yices.expToHOL consts e handle _ => (Const ("[UNTRANSLATED]" ^ s, HOLogic.boolT), consts))
					     val (rest, consts'') = modelify consts' ss
					 in ((s, e, h) :: rest, consts'')
					 end
           val yicesExecutable = case OS.Process.getEnv "ISMT_YICES" of
	   		            SOME s => (Util.trace (fn () => "Using the environment varible ISMT_YICES to invoke yices: " ^ s); s)
				  | NONE   => (Util.trace (fn () => "ISMT_YICES environment variable not set, using default yices"); "yices")
	   val yices = (PipeProcess.launch ("/bin/sh", ["-c", yicesExecutable ^ " " ^ opts ^ " 2>&1"]))
	   	       handle _ => (Util.interfaceError "Cannot launch yices; make sure \"/bin/sh\" exists and \"yices\" is in your path or set the ISMT_YICES environment variable properly.")
       in (YicesBridge.issue yices NONE; (* eat-up initial dump *)
	   let val isOK = YicesBridge.sendWhileOK yices (setup @ types @ defines @ optTypes @ asserts @ [sexpr])
	       val resS = if isOK then YicesBridge.check yices else UNSAT
	       val res = case resS of
			     UNSAT         => UNSAT
			   | SAT model     => SAT (modelify [] model)
			   | UNKNOWN model => UNKNOWN (modelify [] model)
	   in PipeProcess.kill yices;
	      Util.dumpResults res explainModel;
	      res
	   end)
	   handle e => (PipeProcess.kill yices; raise e)
       end
end (* Yices *)

*}

consts ismt_const :: "int \<Rightarrow> 'a" 

(* 
REVISIT: This is what we really wanted to write in order to 
emphasize that ismt_const is injective. But Isabelle rejects this
definition failing to prove the "mono" requirement.

definition ismt_int_to_nat :: "int \<Rightarrow> nat" where
"ismt_int_to_nat i = nat (if i < 0 then 2 * (abs i) - 1 else 2 * i)"


function ismt_nat_const :: "'a itself \<Rightarrow> nat \<Rightarrow> 'a" where
"ismt_nat_const q n = (SOME x. \<forall>m. m < n \<longrightarrow> x \<noteq> ismt_nat_const q m)"

definition ismt_const :: "int \<Rightarrow> 'a" where
"ismt_const i = (\<lambda>n. ismt_nat_const n n) (ismt_int_to_nat i)"
*)

ML 
{* 
structure ismtYices = ISMTInterface(structure backend = Yices); 
structure ISMT = 
struct
  fun setTrace     b = ismtYices.ismt_trace  := b
  fun setTypeCheck b = ismtYices.ismt_tcheck := b
  fun setStats     b = ismtYices.ismt_trace  := b
  fun addAccessor  t = ismtYices.ismt_addAccessor t
end

*}

oracle ismtYicesOracle = {*
    fn (thy, arg) => Thm.cterm_of thy (Multithreading.CRITICAL (fn () =>  ismtYices.ismtSolver thy arg))
*} 

ML 
{* 
fun getSolver mbBackend 
  = case mbBackend of
      NONE         => ismtYicesOracle  (* default solver: Yices *)
    | SOME "Yices" => ismtYicesOracle
    | SOME other   => raise (Fail ("Unknown solver backend: " ^ other))

fun ismt_tac (mbBackend, mode, options) ctxt i 
  = let val solver = getSolver mbBackend 
    in case prems_of i of
       []      => Seq.empty
     | (sg::_) => 
        (let val smtThm = solver (ProofContext.theory_of ctxt, (options, sg))
         in (       (compose_tac (false, smtThm, 0) 1)
             ORELSE (SELECT_GOAL ((rtac smtThm 1) THEN (ALLGOALS atac)) 1)) i
         end)
       handle (err as (THM (msg, _, _))) => (case mode of
                                               "silent" => Seq.empty
                                             | "notify" => (tracing msg; Seq.empty)
                                             | _        => raise err
                                                 
                                            )
    end 
*}

method_setup ismt = 
{* 
  let fun chk m = if (m = "silent" orelse m = "notify" orelse m = "abort") then m
                  else raise (Fail ("Unknown model argument: " ^ m ^ " (should be one of: silent, notify, or abort)"))
      fun spec x = (Scan.repeat (((Args.$$$ "solver" -- Args.colon |-- Args.name) >> (fn b => fn (_, m, (f, t, s, d)) => (SOME b, m, (f, t, s, d         ))))   ||
                                 ((Args.$$$ "model"  -- Args.colon |-- Args.name) >> (fn m => fn (b, _, (f, t, s, d)) => (b,  chk m, (f, t, s, d         ))))   ||
                                 ((Args.$$$ "dump"   -- Args.colon |-- Args.name) >> (fn f => fn (b, m, (_, t, s, d)) => (b,      m, (SOME f, t, s, d    ))))   ||
                                 ((Args.$$$ "tc_on"                             ) >> (fn _ => fn (b, m, (f, _, s, d)) => (b,      m, (f, SOME true,  s, d))))   ||
                                 ((Args.$$$ "tc_off"                            ) >> (fn _ => fn (b, m, (f, _, s, d)) => (b,      m, (f, SOME false, s, d))))   ||
                                 ((Args.$$$ "stats_on"                          ) >> (fn _ => fn (b, m, (f, t, _, d)) => (b,      m, (f, t, SOME true,  d))))   ||
                                 ((Args.$$$ "stats_off"                         ) >> (fn _ => fn (b, m, (f, t, _, d)) => (b,      m, (f, t, SOME false, d))))   ||
                                 ((Args.$$$ "debug_on"                          ) >> (fn _ => fn (b, m, (f, t, s, _)) => (b,      m, (f, t, s, SOME true ))))   ||
                                 ((Args.$$$ "debug_off"                         ) >> (fn _ => fn (b, m, (f, t, s, _)) => (b,      m, (f, t, s, SOME false)))))

                    >> ((fn f => f (NONE, "notify", (NONE, NONE, NONE, NONE))) o curry (Library.foldl (op o)) I o rev)) x
  in
    Scan.lift spec >> (fn args => fn ctxt => Method.SIMPLE_METHOD (ismt_tac args ctxt))
  end
*}
  "Interface to the Yices SMT solver"
end
