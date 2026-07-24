\documentclass[11pt]{article}
\usepackage{eepic}
\usepackage[utf8x]{inputenc}
\usepackage{palatino}
\usepackage[margin=2.5cm]{geometry}
\usepackage{titlesec}
\usepackage{enumitem}
\usepackage{mdframed}
\usepackage{xcolor}
\usepackage{parskip}
\usepackage{hyperref}
\usepackage{booktabs}
\usepackage{array}
\usepackage{graphicx}
\usepackage{float}
\usepackage{booktabs}
\usepackage{xcolor}
\usepackage{fleqn}
\usepackage{url}
\usepackage{hyperref}
\usepackage[all]{xy}

%include polycode.fmt
%%include lhsmacros.sty

\begin{document}

\vspace{7mm}
\fontsize{12pt}{17pt}\selectfont
{\Large
\textbf{Universidade do Minho}
\\
{\fontseries{l}\selectfont
School of Engineering
}}

\vspace{50mm}
\fontsize{20pt}{27pt}\selectfont
{\huge
\textbf{Project in \href{https://haslab.github.io/MFP/}{Formal Methods in Programming}}
\\
Final Report}
\\
%
{\LARGE
MSc\ Software Engineering
}

\vspace{50mm}
\fontsize{12pt}{17pt}\selectfont
\begin{itemize}
    \item Cláudia Faria (PG60240)
    \item Patrícia Bastos (PG60287)
    \item[] Supervisor: José N. Oliveira (DIUM \& INESC TEC)
\end{itemize}

\vspace*{\fill}
{\large \today}

\newpage

\tableofcontents

\newcommand{\eqlabel}[1]{\refstepcounter{equation}\label{#1}(\theequation)}
\newenvironment{minip}[1]{\begin{eqnarray}\label{#1}\begin{minipage}{.95\textwidth}\vskip -1ex}{\end{minipage}\end{eqnarray}}
\def\conj#1#2{\mathopen{\langle} #1, #2 \mathclose{\rangle}}
\def\just#1#2{\\ &#1& \rule{2em}{0pt} \{ \mbox{\rule[-.7em]{0pt}{1.8em} \small #2 \/} \} \nonumber\\ && }
\def\start{&&}
\def\more{\\&&}
\def\conv#1{#1^\circ}
\def\alt#1#2{\mathopen{[}#1\hskip 1pt,#2\mathclose{]}}
\def\crflx#1{\Phi_{#1}}
\def\rcb#1#2#3#4{\def\nothing{}\def\range{#3}\mathopen{\langle}#1 \ #2 \ \ifx\range\nothing::\else: \ #3 :\fi \ #4\mathclose{\rangle}}
\newenvironment{lcbr}{\left\{\begin{array}{l}}{\end{array}\right.}
\renewenvironment{cases}{\left\{\begin{array}{ll}}{\end{array}\right.}
\def\implied{\mathbin\Leftarrow}
\def\implies{\mathbin\Rightarrow}
\def\tag#1{\relax}
\def\larrow#1#2#3{\xymatrix{ #3 & #1 \ar[l]_-{#2} }}
\def\rarrow#1#2#3{\xymatrix{ #1 \ar[r]^-{#2} & #3 }}
\def\N{\mathbb{N}\index{Números naturais ($\mathbb{N}$)}}

%format (St f)  = "{" f "}_{St}" 
%format (ln n)  = "\vert " n "\vert"
%format (pw (n)) = "2^{" n "}"
%format (ceil (f)) = "\lceil " f "\rceil"
%format p1  = "\pi_1 "
%format p2  = "\pi_2 "
%format atmost = " \subseteq "
%format atleast = " \supseteq "
%format (anaList (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format ins = "\mathbin\in "
%format (lcbr4 (x)(y)(z)(w)) = "\begin{lcbr}" x "\\" y "\\" z "\\" w "\end{lcbr}"
%format exists = "\exists "
%format (rcb q (v) (r) (t)) = "\rcb{"  q "}{" v "}{" r "}{" t "}"
%format <=> = "~\Leftrightarrow~"
%format (cup3 (a)(b)(c)) = "\left\{ \begin{array}{ll} &{"  a  "}\\ \cup &{"  b  "}\\ \cup &{"  c  "}\end{array}\right."
%format (cup4 (a)(b)(c)(d)) = "\left\{ \begin{array}{ll} &{"  a  "}\\ \cup &{"  b  "}\\ \cup &{"  c  "}\\ \cup &{" d "}\end{array}\right."
%format (vee4 (a)(b)(c)(d)) = "\left\{ \begin{array}{ll} &{"  a  "}\\ \vee &{"  b  "}\\ \vee &{"  c  "}\\ \vee &{" d "}\end{array}\right."
%format (crflx (p)) = "\crflx{" p "}"
%format (const (x)) = "\underline{" x "}"
%format g2 = "g_{2}" 
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (cup (a)(b)) = "{" a "}\mathbin\cup{" b "}"
%format (conv (r)) = "\conv{" r "}"
%format (conv2 (r)) = "({\conv{" r "}})^{\circ}"
%format . = "\mathbin{\cdot}"
%format (floor (f)) = "\lfloor " f "\rfloor"
%format (logBase (n) (e)) = "\mathit{log}_{" n "}{" e "}"
%format (cataList (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (unfoldr (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format inj0 = "inj_{0}"
%format inj10 = "inj_{10}"
%format inj110 = "inj_{110}"
%format inj111 = "inj_{111}"
%format >< = " \times "
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (curry (f)) = "\overline{" f "}"
%format (uncurry (f)) = "\widehat{" f "}"
%format xor = "\oplus "
%format .|. = "\vee "
%format `xor` = "\mathbin\oplus "
%format (vI (t))  = "\mathbf{I}_{" t "}"
%format ot = "\mathbf{o}_t"
%format (vM (t))  = "\mathbf{M_{" t "}}"
%format (vR (t))  = "\mathbf{R_{" t "}}"
%format (vB (t))  = "\mathbf{B_{" t "}}"
%format (vD (t))  = "\mathbf{D_{" t "}}"
%format (dot (a)) = "\dot{" a "}"
%format (dotp (t)) = "\dot p_{" t "}"
%format (dotr (t)) = "\dot r_{" t "}"
%format (dotf (t)) = "\dot f_{" t "}"
%format (vI (t)) = "\mathbf{I_{" t "}}"
%format (vu (t)) = "\mathbf{u_{" t "}}"
%format (vq (t)) = "\mathbf{q_{" t "}}"
%format (vc (t)) = "\mathbf{c_{" t "}}"
%format (vC (t)) = "\mathbf{C_{" t "}}"
%format (vV (t)) = "V_{" t "}"
%format (vX (t)) = "X_{" t "}"
%format (vh(t)) = "\mathbf{h_{" t "}}"
%format (v_o (t)) = "\mathbf{o_{" t "}}"
%format (neg (t)) = "\neg {" t "}"
%format (Phi (t)) = "\Phi_{" t "}"
%format alpha = "\alpha"
%format d1 = "d_{1}"
%format d2 = "d_{2}"
%format d3 = "d_{3}"
%format d4 = "d_{4}"
%format d5 = "d_{5}"
%format d6 = "d_{6}"
%format ddot = "{\dot d}" 
%format e1 = "e_{1}"
%format e2 = "e_{2}"
%format e3 = "e_{3}"
%format e4 = "e_{4}"
%format e5 = "e_{5}"
%format e6 = "e_{6}"
%format equiv = "\equiv"
%format fBit = "{\dot f}" 
%format fDec = "f_{Dec}" 
%format fEnc = "f_{Enc}" 
%format fH = "f_{H}" 
%format fQ = "f_{Q}" 
%format fU = "f_{U}" 
%format funcD = "func_{D}" 
%format funcV = "func_{V}" 
%format gB = "g_{B}" 
%format gD = "g_{D}" 
%format gDec = "g_{Dec}" 
%format gEnc = "g_{Enc}" 
%format gM = "g_{M}" 
%format i0 = "i_{0}" 
%format i1 = "i_{1}" 
%format i2 = "i_{2}" 
%format i3 = "i_{3}" 
%format i4 = "i_{4}" 
%format i5 = "i_{5}" 
%format i6 = "i_{6}" 
%format m1 = "m_{1}" 
%format maskZero = "M_{0}"
%format newH  = "new_{H}" 
%format newQ  = "new_{Q}" 
%format newU  = "new_{U}" 
%format next = "next" 
%format o0 = "o_{0}" 
%format o1 = "o_{1}" 
%format o2 = "o_{2}" 
%format o3 = "o_{3}" 
%format o4 = "o_{4}" 
%format o5 = "o_{5}" 
%format o6 = "o_{6}" 
%format rArrow = "\rightarrow"
%format rBit = "{\dot r}" 
%format s0d = "s_{0d}"
%format s0e = "s_{0e}"
%format s1d = "s_{1d}"
%format s1e = "s_{1e}"
%format s2d = "s_{2d}"
%format s2e = "s_{2e}"
%format s3d = "s_{3d}"
%format s3e = "s_{3e}"
%format s4d = "s_{4d}"
%format s4e = "s_{4e}"
%format s5d = "s_{5d}"
%format s5e = "s_{5e}"
%format s6d = "s_{6d}"
%format s6e = "s_{6e}"
%format sid = "s_{id}"
%format sie = "s_{ie}"
%format vecC = "vec_{C}" 
%format vecE = "vec_{E}" 
%format vecK = "vec_{K}" 
%format vecX = "vec_{X}" 
%format vecY = "vec_{Y}" 
%format Nat0 = "\N_0"
%format inNat = "\textit{in}_{\N_0}"
%format outNat = "\textit{out}_{\N_0}"

% Colors
\definecolor{boxbg}{HTML}{F5F5F5}
\definecolor{boxborder}{HTML}{CCCCCC}
\definecolor{titlegray}{HTML}{333333}

% Section formatting


% Colors
\definecolor{boxbg}{HTML}{F5F5F5}
\definecolor{boxborder}{HTML}{CCCCCC}
\definecolor{titlegray}{HTML}{333333}

% Section formatting
\titleformat{\section}{\large\bfseries\color{titlegray}}{}{0em}{}[\titlerule]
\titleformat{\subsection}{\normalsize\bfseries\color{titlegray}}{}{0em}{}

% Framed box style
\mdfdefinestyle{componentbox}{
  backgroundcolor=boxbg,
  linecolor=boxborder,
  linewidth=0.8pt,
  innerleftmargin=12pt,
  innerrightmargin=12pt,
  innertopmargin=10pt,
  innerbottommargin=10pt,
  skipabove=8pt,
  skipbelow=8pt,
  roundcorner=4pt
}

\newenvironment{componentbox}[1]{%
  \begin{mdframed}[style=componentbox]%
  \textbf{#1}\\[4pt]%
}{%
  \end{mdframed}%
}

\hypersetup{
  colorlinks=true,
  linkcolor=black,
  urlcolor=blue
}

\title{\textbf{Formal verification of the Pocket\texttt{+} lossless compression algorithm}}
\date{}

\maketitle
\vspace{-1em}
\hrule
\vspace{1.5em}

\part{Report} 

% ──────────────────────────────────────────────
\section{Introduction}

POCKET+ is a lossless compression algorithm for spacecraft housekeeping telemetry, designed to compress fixed-length telemetry 
packets individually, as they are generated, using only low-level bitwise operations. This makes it lightweight enough to run on 
flight hardware, and its built-in robustness to packet loss makes it suitable for the unreliable communication links typical of 
space missions. It is the CCSDS Recommended Standard For Robust Compression of Fixed-Length Housekeeping Data \cite{CCSDS124B1}.

Among all the advantages of this algorithm, two stand out the most: it makes compression performance more predictable for all 
packets, reducing important parameters such as worst compression rate and standard deviation, and it significantly reduces the 
amount of design work required to select telemetry acquisitions, rates, and the introduction of asynchronous events.

There already exist implementations of this protocol and articles considering the effect of flags on the standard's compression 
efficiency, as analyzed in \cite{10460536}. But despite operating in environments where data integrity is crucial, a proof of 
correctness for POCKET+ is yet to be made. Proving that this compression algorithm is correct means showing that after the compression 
of a certain input, the output of its decompression does not differ from that input. This means that no information is lost or 
incorrectly reconstructed, in the case of packet losses. 

This project was requested by the company Telespazio and aims to provide such proof by implementing the algorithm in Haskell, whose 
mathematical foundations make it the perfect choice for translating the code into algebraic specifications. Relational algebra will then 
be used to assist and provide the algorithm's correctness. 

% ──────────────────────────────────────────────
\section{Protocol}

The POCKET+ protocol is a lossless compression algorithm designed for fixed-length housekeeping data. Its goal is to 
efficiently encode sequences of binary input vectors by identifying redundancy between successive packets. 
The protocol consists of four main components: 

\begin{table}[H]
  \centering
  \caption{The core of the protocol}
  \label{tab:protocol-core}
  \begin{tabular}{ll}
  \toprule
  \textbf{Component} & \textbf{Purpose} \\
  \midrule
  Flags and Parameters & Mostly user-specified, determine the protocol's behaviour \\
  Mask Update & Identifies predictable bits \\
  RLE & Packet encoding function \\
  Resynchronization & Restores information lost \\
\bottomrule
\end{tabular}
\end{table}

\vspace{1em}
\hrule
\vspace{0.5em}

\subsection{Parameters and Definitions}

The parameters and definitions used in the protocol are essential for understanding how the Mask Update and 
Encoding stages work and provide the necessary context for interpreting the operations performed by the 
Encoder and Decoder.

The user can choose to specify certain parameters that influence the behavior of the compressor, such as the 
initial mask vector and a flag that determines whether to include the entire input vector in the output. 
These parameters allow for flexibility and can be adjusted based on the specific requirements of the data. 

The two most important parameters are always user-defined and essential for the packet loss robustness properties 
of the protocol. 

The flag that controls the inclusion of the entire input vector in the output is particularly important, as it 
allows for a trade-off between compression efficiency and the ability to recover from data loss. By including 
the entire input vector, the compressor can ensure that all information is preserved, but it may result in larger 
output sizes. On the other hand, by only including the unpredictable bits, the compressor can achieve better 
compression ratios, but it may be more susceptible to data loss.

Similarly, the minimum required effective robustness level parameter allows the user to specify how many 
consecutive output vectors can be lost without affecting the ability to decompress the data and providing a 
guarantee of the compressor's resilience to packet loss.

\begin{componentbox}{User-Specified Variables}
\begin{description}[leftmargin=1.8cm, labelwidth=1.6cm, style=nextline]

  \item[\textbf{New Mask flag (\textit{p})}]
    Indicates whether the Mask will be replaced, enabling bit positions to change
    classification from unpredictable to predictable if they have not changed state
    since the last time.

  \item[\textbf{Send Mask flag (\textit{f})}]
    Causes the entire mask vector to be encoded in the output vector when set to one.

  \item[\textbf{Uncompressed flag (\textit{r})}]
    Causes the entire input vector to be included in the output vector when set to one.

  \item[\textbf{Minimum Required Robustness Level (\textit{R})}]
    Controls the guaranteed number of consecutive output vectors that can be lost prior
    to the current output vector without affecting the ability to decompress it.
    The effective value will always be equal to or greater than this.

\end{description}
\end{componentbox}

% ──────────────────────────────────────────────
\vspace{0.5em}
\begin{componentbox}{Cycles}
A \textbf{cycle} is a complete run of the Mask Update and Encoding operations, with
the full rotation of the parameters.

\medskip
Cycles are relevant in:
\begin{itemize}[leftmargin=1.5em, itemsep=2pt]
  \item \textbf{Section 5.3.2.2} --- when counting consecutive occurrences of no mask
        changes, starting from the first cycle not covered by the minimum required
        effective robustness level.
  \item \textbf{Section 5.3.3.1} --- when using the above count for OR-ing Changes.
\end{itemize}
\end{componentbox}

% ──────────────────────────────────────────────
\vspace{0.5em}
\begin{componentbox}{Predictable Bits}
A bit is \textbf{predictable} when, for that same index, two consecutive input vectors
have the same value.

\medskip
\begin{table}[H]
  \centering
  \label{tab:predictable-bits}
  \begin{tabular}{ll}
  \toprule
  \textbf{Value} & \textbf{Meaning} \\
  \midrule
  0 & The two input vectors have the \emph{same} bit for that index. \\
  1 & The two input vectors have a \emph{different} bit for that index. \\
\bottomrule
\end{tabular}
\end{table}
\end{componentbox}

\vspace{1em}
\hrule
\vspace{0.5em}

% ──────────────────────────────────────────────
\subsection{Mask Update}

The core idea of POCKET+ is that most housekeeping telemetry values don't change between successive packets.

The Mask Update operation identifies redundancy - predictable bits - between the packets. It is based on 
Differential pulse-code modulation (DPCM), which changes between consecutive samples of a signal, rather 
than the signal's value directly \cite{dpcm}. DPCM is then decoded by integrating DPCM samples over time.

To better understand the concept behind the Mask Update, we can think of the Input as having some sort of "discrete
derivatives". The Mask Update identifies which bits of the input vector are changing, and which are not, by 
comparing the current input vector with the previous one. The bits that are changing are marked as unpredictable, 
while the bits that remain the same are marked as predictable. This information is then used in the encoding 
process to efficiently compress the data by only encoding the unpredictable bits. The Change vector, which 
indicates which bits of the mask have changed between cycles, can be thought of as a "second derivative" of 
the input vector, as it captures the changes in the predictability of the bits over time.

\begin{figure}%[H]
  \centering
  \includegraphics[width=0.4\textwidth]{images/derivatives.png}
  \caption{Mask Update "discrete derivatives"}
  \label{fig:derivatives}
\end{figure}

There are three main components in the Mask Update: Mask, Build, and Change. They are all calculated based on the 
exclusive-or between the current input vector and the previous one.

\begin{componentbox}{Mask}
Identifies (\textsc{xor}) unpredictable bits.

Compares (\textsc{or}) with the last calculated difference (Mask or Build, based on
user-defined $p$).

\medskip
\begin{itemize}[leftmargin=1.5em, itemsep=3pt]
  \item \textbf{Mask bit = 0} if both the current \textsc{xor} and the previous mask
        are 0 $\Rightarrow$ the bit has been stable across both steps.
  \item \textbf{Mask bit = 1} if either the current \textsc{xor} or the previous mask
        is 1 $\Rightarrow$ the bit is, or recently was, unpredictable.
\end{itemize}
\end{componentbox}

\begin{componentbox}{Change}
Identifies which bits of the mask changed.

\medskip
\begin{itemize}[leftmargin=1.5em, itemsep=3pt]
  \item \textbf{0} --- the mask bit is the same as the previous mask bit; predictability
        status is unchanged.
  \item \textbf{1} --- the mask bit differs from the previous mask bit; a bit has become
        predictable or unpredictable.
\end{itemize}
\end{componentbox}

\begin{componentbox}{Build}
Accumulates the same information as Mask in parallel, but \textbf{resets to zero when
$p = 0$}, marking all positions as predictable.

\medskip
This enables bit positions to change classification from unpredictable to predictable
if they have not changed state since the last time the new mask flag was set to one.
\end{componentbox}

\vspace{1em}
\hrule
\vspace{0.5em}

% ──────────────────────────────────────────────
\subsection{Encoding}

Run-length Encoding (RLE) is a common and simple form of lossless data compression in which consecutive
occurrences of the same data are stored as a single data value and count. Once the unpredictable bits have been 
isolated, RLE is applied to encode the changes of the mask itself (our “second derivative”), which indicates 
which bits of the mask have changed between cycles. The Change vector will have long runs of 0s (predictable bits) 
that RLE will handle efficiently.

In the Encoding, the output vector is a concatenation of three variable-length binary vectors, H, Q, and U, 
which encode different information about the input vector and the mask. The exact content of these vectors 
depends on the user-specified parameters and the current state of the mask.

\begin{componentbox}{H}
Encodes the positions in the mask vector that have changed over a number of cycles and
indicates whether each change resulted in a predictable or unpredictable classification.

\medskip
Specifically encodes \textbf{Mask Change + Effective Robustness Level + Help structures}.

\medskip
\textbf{Mask Change (X)}\\[3pt]
Run-Length Encoding applied to Change vectors OR-ed together. The amount of previous
Changes considered is the \emph{number of cycles} demanded by the current minimum
required robustness level.

\medskip
\textbf{Effective Robustness Level (V)}\\[3pt]
Number of cycles that are included in the mask change information for this cycle.

\medskip
\textbf{Help Structures}
\begin{description}[leftmargin=0.8cm, style=nextline, itemsep=3pt]
  \item[\textit{e} and \textit{k}] Indicate information on the mask values for each change.
  \item[\textit{c}] Indicates if $p$ was set to one more than once in the last cycles.
        Some bits may have transitioned from unpredictable to predictable, so those bits
        need to be explicitly included in U alongside the unpredictable bits.
  \item[\textit{d}] Indicates if $f$ and $r$ are both zero, meaning there is no requested
        new mask and the header is already sufficient to describe the block, so no
        additional flag is needed in U. Serves to indicate no dependencies from previous packets.
\end{description}
\end{componentbox}

\begin{componentbox}{Q}
Encodes the Mask by only transmitting it when \texttt{sendMask} is set and no new mask
is incoming.

\medskip
\begin{itemize}[leftmargin=1.5em, itemsep=4pt]
  \item \textbf{If $f = 1$:} Encodes the entire mask. XORs the mask against a shifted
        version of itself, computing the \emph{difference between adjacent bits} of the
        mask rather than the bits themselves, then RLE-encodes the result.
  \item \textbf{If $f = 0$ and $r = 0$:} Encodes nothing --- can be decoded from the
        mask changes.
  \item \textbf{If $f = 0$ and $r = 1$:} Encodes no change.
\end{itemize}
\end{componentbox}

\begin{componentbox}{U}
Encodes a copy of the input vector or the unpredictable bits.

\medskip
\textbf{If $r = 1$ (block is uncompressed):}
\begin{itemize}[leftmargin=1.5em, itemsep=2pt]
  \item Encodes the \textbf{length of the input vector} + full input copy.
\end{itemize}

\medskip
\textbf{If $r = 0$ (block is compressed):}
\begin{itemize}[leftmargin=1.5em, itemsep=2pt]
  \item If $c = 1$: encodes the \textbf{unpredictable bits} + bits that have gone from
        unpredictable to predictable.
  \item If $c = 0$: encodes \textbf{only the unpredictable bits}.
\end{itemize}

\medskip
\textit{Note:} $f = 1$ adds a \texttt{0} flag at the start for header disambiguation
purposes.
\end{componentbox}

\vspace{1em}
\hrule
\vspace{0.5em}

\subsection{Robustness to packet loss}

The highlight of the protocol is its robustness to packet loss, which is achieved through a resynchronization process during the
decoding. When a packet is lost, the Decoder can use the information from the subsequent packets to recover the original input vector.

\begin{figure}%[H]
  \centering
  \includegraphics[width=1\textwidth]{images/resync.png}
  \caption{Decoding with packet loss}
  \label{fig:resync}
\end{figure}

Focus will not be given to this component, as it is not currently implemented at the time of this report.

% ──────────────────────────────────────────────
\section{Implementation}

There already exists a Pocket+ implementation in C++ by Vision Space \cite{visionspace}, but it is not formally verified. Our goal is to 
provide a Haskell implementation that can be formally verified using relational algebra. Therefore, the implementation will be done 
from scratch, following the specifications provided in the standard and using the C++ implementation as a reference for testing and 
validation.

The first thing to be noted in this protocol is that the Encoder is a finite state machine, split into the Mask 
Update and the Encoding stages. The Mask Update calculates the Mask, Build, and Change vectors, which make up the 
cycle's state, while the Encoding stage calculates the output vector based on the input vector and the 
compressor parameters. Essentially, at each cycle, the protocol creates a new state based on the previous state 
and the current input, and then produces an output based on that new state and the current input. This behaviour is
that of a Mealy Machine.

A Mealy Machine is a special type of machine in finite automata theory where the output is 
determined by both the current state and the current input. A Mealy Machine can produce 
different outputs for the same state based on different inputs. It has two transition functions:

\begin{itemize}[leftmargin=1.5em, itemsep=4pt]
  \item \textbf{State transition function: }defines how the machine moves from one state to 
  another based on the input.
  \item \textbf{Output transition function: }specifies the output produced for each input 
  given to a state.
\end{itemize}

To set up our Mealy Machine, we will compose two pairs of functions. The first pair will be responsible for the state transition, 
while the second pair will be responsible for the yielding the output. In Haskell, it will be defined as,

\[
m = \langle \pi_1, f \rangle \cdot \langle g, \pi_2 \rangle
\]

\noindent where |p1| and |p2| are the projection functions that extract the new state and the output, respectively. 

\begin{figure}%[H]
  \centering
  \includegraphics[width=0.5\textwidth]{images/mealy1.png}
  \caption{Mealy Machine}
  \label{fig:mealy1}
\end{figure}

Essentially, the first pair $\langle \pi_1, f \rangle$ will take the current state and input and produce the new state, while the 
second pair $\langle g, \pi_2 \rangle$ will take the new state and input and produce the output.

\begin{figure}%[H]
  \centering
  \includegraphics[width=0.6\textwidth]{images/mealy2.png}
  \caption{A Closer Look At The Mealy Machine}
  \label{fig:mealy2}
\end{figure}

Each cycle of the Encoder can be seen as application of the Mealy Machine, where each state is contains the Mask, Build, 
and Change vectors along with the last Input vector, length of the vectors, and parameters. The input is the current input vector, and 
the output is the concatenation of the H, Q, and U vectors.

Similarly, the Decoder will also behave as a Mealy Machine, where the state will be the same, the input
will be the current output vector to be decoded, and the output will be the original recovered input vector.

% ──────────────────────────────────────────────
\section{Correctness}

For the proofs in this report, we will be using relational algebra, which provides a powerful framework for 
reasoning about the properties of relations, and therefore functions, and their compositions \cite{pdbc}.
We will make use of converses and pointfree  decomposition of the main components' functions and properties to 
aid our proof of correction. Additional correctness details are provided at the end of this document.

The goal of the Pocket+ protocol is to ensure that the output of the Decoder is always the same as the original input vector that was fed
to the Encoder. We might think of the Encoder and Decoder as two relations, where:
\begin{eqnarray}
	|Decoder = conv Encoder|
\end{eqnarray}
This is, however, too strong. For a compressing and decompressing protocol, it is enough that:
\begin{eqnarray}
	|Decoder . Encoder = id|
\end{eqnarray}

This means that the composition of the Decoder and Encoder relations is the identity relation, which implies that for every input vector,
the output of the Decoder after encoding and then decoding will be the same as the original input vector. 

However, this proof is far from trivial. The Encoder and Decoder are complex functions with many components, and due to the presence 
of user-specified parameters and robustness adjustments, the two don't mirror each other perfectly. This is a consequence of the 
protocol's design, which prioritizes compression performance and robustness over simplicity. Therefore, for now, we will break down the 
proof into smaller components that make up the core the compression and show that each of those components is correct.

\subsection*{Reversibility}

Lossless compression implies no information is lost during the encoding and decoding process. This makes reversibility our primary concern, 
which can be ensured with minimal complements \cite{reversibility}. Essentially, a minimal complement of a 
function contains just enough information that was originally missing to make it reversible. By attaching this minimal
complement, the function becomes injective, and thus reversible. 

\subsection*{Run-length Encoding}

\def\X{
\section{Imported modules}

\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
import Data.List (mapAccumL,unfoldr,intercalate, subsequences)
import Lib.Cp hiding (i1,i2)
import Lib.Data_List_Split_Internals hiding(split)
import Lib.List
import Lib.Nat
import Lib.St 
import Data.Bits 
\end{code}
}
Considering the functions' signatures, we can see that the RLE function is not injective, as |unrle| requires an integer parameter,
the length of the original vector, to be able to complete the remaining zeros. 

\begin{spec}
rle :: [Bit] -> [Bit]
\end{spec}

\begin{spec}
unrle :: [Bit] -> Int -> [Bit]
\end{spec}

However, by attaching this length as a minimal complement to the RLE function, we can make it injective and thus reversible.
By implementing the run-length encoding, with minimal complements, we will ensure that the heart of the compression is reversible and 
correct-by-construction.
Then, all that is left is uncurrying the decoding function, and we obtain the following reversible pair of functions:

\begin{code}
rle'   :: ([Bit] -> ([Bit], Int))
rle' = split rle length
\end{code}

\begin{code}
unrle' :: ([Bit], Int) -> [Bit]
unrle' = uncurry unrle
\end{code}

Although the recovering of the zeros in not important in the context of the protocol, it is essential for the proof of correctness, 
as it allows us to show that the RLE functions are inverses of each other. Naturally, this isn't done just yet.
The next step is to look at the definition of the RLE functions and see how we can decompose it into smaller functions that are 
easier to analyze and prove correct. This proof can be found at the end of this document and ensures the correctness of this core
component of compression.

\subsection*{Bit extraction}

After run-length encoding, another important compression operation is the bit extraction, which is responsible for extracting only 
the unpredictable bits from the input vector. The bit extraction operation extracts the bits at positions where the mask signals a 
change, discarding the rest that can be predicted from the previous input vector. During the decoding process, the patch function takes 
the extracted bits and reinserts them into their original positions based on the mask, reconstructing the original input vector.

Together they implement the compression: the encoder sends only the unpredictable bits and the decoder puts them back into the right 
slots. However, this doesn't mean that they are inverses of each other. In fact, the bit extraction function is not injective, as 
different input vectors can yield the same extracted bits. The proof is then made even more difficult by the number of 5 cases in 
the encoding of the third sub-vector, which depend on the user-specified parameters.

\subsection*{Robustness}

The components relevant to robustness are the Change vector and the effective robustness level. The Change vector identifies which 
bits of the mask have changed between cycles, while the effective robustness level determines how many previous cycles' changes are 
considered when encoding the changes in the current cycle in vector |vX()|. The effective robustness level must be equal to or greater 
than the minimum required effective robustness level specified by the user, which is always true, by definition of |vV()| in section 
5.3.2.2, where |vC()|, which counts occurrences, is always a positive integer.

The |vX()| is then encoded in the first sub-vector of the output and necessary in the encoding of the input vector in the third-subvector,
when |vc()| is 1, to encode that extra information. 

The Pocket+ protocol encodes extra information at certain cycles, as specified by the user, to ensure that the decoder can recover from 
packet losses through the resynchronization process. However, this report does not implement the resynchronization process at this time.

% ──────────────────────────────────────────────
\section{Discussion}

The encoder and decoder are not perfect mirrors of each other, as the protocol's design prioritizes compression performance and 
robustness over simplicity. Finding direct converses is not enough, and the chosen approach was to break down the proof into smaller 
components that make up the core of the compression and show that each of those components is correct. 

The 124.0-B-1 Standard itself is not a simple read. The presence of user-specified parameters and robustness adjustments makes the 
implementation and proof of correctness more difficult. Having struggled with the standard, we hoped to create a simpler but richer
formal specification of the protocol, complete with descriptive diagrams to aid in comprehension. This specification can be found at the 
end of this document, along with the respective code, and we hope it can be used as a reference for future work on the protocol.

Haskell was chosen to implement the protocol due to its strong type system and mathematical foundations, which make it easier to 
translate the code into algebraic specifications and reason about its properties. Even if the reader is not fluent in Haskell, the code,
equipped with diagrams, should be easy to understand and follow. With Haskell, we translated the Mealy Machine structure of the protocol 
into a composition of two pairs of functions, one for the state transition and another for the output generation. This structure allowed us to
reason about the protocol's behavior in a modular way, analyzing the state transitions and output generation separately.

% ──────────────────────────────────────────────
\section{Conclusion and Future Work}

The protocol implementation started in February 2025, as part of the final project of the Bachelor's in Computer Science. In June 2026,
now under the final project of Formal Methods of Programming in the Master's in Software Engineering, the implementation was completed, 
and the proof of correctness started. The proof is still work in progress, with focus on the main components of the protocol, such as 
the RLE and bit extraction functions, and the robustness properties. The final goal is to show that the composition of the Decoder and 
Encoder relations is the identity relation, proving the correctness of the protocol.

Currently, the next step of this implementation is cross-validation for compliance with the four corpora of housekeeping
telemetry data defined by the CCSDS Data Compression working group. 
Future work regarding the proof of correctness includes completing the existing proofs and further exploring the role of the
user-specified parameters in the protocol's behavior and correctness. Additionally, the resynchronization process can be implemented, as 
a crucial step to the conclusion of this implementation.

This report contributes with a richer formal specification of the protocol, an implementation in Haskell to be used as a
reference for testing and validation, and a proof of correctness for the main components of the protocol, which are essential for its 
correctness, using relational algebra. 

This work lays the foundation for a complete proof of correctness for the Pocket+ protocol, and perhaps encourage further research into 
the formal verification of similar algorithms with critical applications, where correctness is of utmost importance.

% ──────────────────────────────────────────────
\bibliographystyle{plain}
\bibliography{references}

\newpage \small

\part{CCSDS Standard}

\section*{3 INPUTS AND PARAMETERS}
\subsection*{3.1 OVERVIEW}
The compressor losslessly encodes a sequence of length-F binary input vectors |vI t|, |t = 0, 1, ...|
At each time index t, the compressor produces a variable-length binary output vector |v_o t| that
losslessly encodes |vI t|. This encoding depends on several user-specified variables defined in 3.2:
\begin{itemize}
\item The initial mask vector, |vM 0|, is a length-F binary vector used to initialize the mask.
\item The minimum required effective robustness level, |R t|, controls the guaranteed number
of consecutive output vectors that can be lost prior to the current output vector
without affecting the ability to decompress it. The effective robustness level will be
equal or greater than this value.
\item The new mask flag, |dotp t|, when set to one, causes the current mask vector to be replaced
with the mask being built. This enables bit positions to change classification from
unpredictable to predictable if they have not changed state since the last time the new
mask flag was set to one.
\item The uncompressed flag, |dotr t|, causes the entire input vector to be included in the output
vector when it is set to one; otherwise, only those bits classified as unpredictable are
included.
\item The send mask flag, |dotf t| causes the entire mask vector to be encoded in the output
vector when it is set to one.
All compressor parameters needed for decompression can be determined from the output
binary vectors.
\end{itemize}
\subsection*{3.2 INPUT}
At each time index |t = 0, 1, ...|, the input to the compressor shall be a length-F binary input
vector |vI t|, where the input vector length |F| shall be a user-specified integer in the range $1 \leq F \leq 2^{16} - 1$.

\subsection*{3.3 PARAMETERS}
\subsubsection*{3.3.1} The user-specified initial mask vector, |vM 0|, shall be a length-F binary vector.

NOTE --- |vM 0| could be derived from analysis of previous mask values or a stored value of
the mask from the last time this was run. Setting |vM 0 = 0| (i.e., all positions
predictable) is often a reasonable default.

\subsubsection*{3.3.2} In addition to the initial mask vector, compression parameters at each time index |t| consist of the following:

\begin{enumerate}[label=\alph*)]
\item 
The user-specified minimum required effective robustness level, |R t|, which shall be an integer between 0 and 7 at each time index |t|.
\item 
The user-specified new mask flag, |dotp t|, which shall be zero or one at each time index |t|.
\item
The send mask flag,|dotf t|, which shall be $|dotf t| = 1$ for $t\leq |Rt|$; otherwise, |dotf t| is user-specified and shall be zero or one.
\item
The uncompressed flag, |dotr t|, which shall be $|dotr t| = 1$ if $t \leq |Rt|$; otherwise |dotr t| is user-specified and shall be zero or one.
\end{enumerate}

NOTE --- The values of user-specified parameters |vM 0|, |R t|, |dotf t|, |dotp t|, and |dotr t| need not be known in advance, or communicated via means external to the compressor, for	successful decompression.

\section*{4 MASK UPDATE}

\subsection*{4.1 OVERVIEW}
This section specifies the compressor's mask update stage. Two binary vectors, |vM t| (the
mask) and | vB t| (the build), are updated in parallel based on the exclusive-or between the current input binary vector and the previous one (see 4.2.1 and 4.2.2).

Since no such difference is defined for the first input vector, build is initialized to a zero vector, that is, $|vB  0| = 0$. For subsequent input binary vectors, a bitwise XOR of sequential input binary vectors is used to update mask and build. The change vector, | vD t| is computed as the exclusive-or between the current mask and previous mask (see 4.2.3).

When the new mask flag, |dotp t|, is set to one, the mask is replaced by build, and build is reset to a zero vector; that is, all positions are classified as predictable (see 3.3.2). Hence, even though the update processes for mask and build depend on the same calculations, these vectors are not in general identical because they may be reset at different times during the
encoding process.
\subsection*{4.2 MASK UPDATE}

\subsubsection*{4.2.1}
For $t \geq 0$, the build vector is a length-F binary vector defined as

\begin{equation}
    | vB t| = \begin{cases} 
        (|vI t| \text{ XOR } |vI (t-1)|) \text{ OR } |vB  (t-1)|, & t > 0, |dotp t| = 0 \\ 
        \mathbf{0}, & \text{otherwise} 
    \end{cases},
\end{equation}

where |dotp t| is defined in 3.3.2.

\subsubsection*{4.2.2}
For $t > 0$, the mask vector is a length-F binary vector defined as

\begin{equation}
    |vM t| = \begin{cases} 
        (|vI t| \text{ XOR } |vI (t-1)|) \text{ OR } |vM (t-1)|, & |dotp t| = 0 \\ 
        (|vI t| \text{ XOR } |T (t-1)|) \text{ OR } |vB  (t-1)|, & \text{otherwise} 
    \end{cases},
\end{equation}

where |dotp t|  is defined in 3.3.2.

NOTE --- At $t = 0$, the initial mask vector |vM 0| is user-specified (see 3.3.1).

\subsubsection*{4.2.3}
For $t \geq 0$, the change vector | vD t| is a length-F binary vector defined as

\begin{equation}
     | vD t| = \begin{cases} 
        |vM t| \text{ XOR } |vM (t-1)|, & t > 0 \\ 
        \mathbf{0}, & \text{otherwise} 
    \end{cases}.
\end{equation}

\section*{5 ENCODER}
\subsection*{5.1 OVERVIEW}

This section specifies the encoding stage of the compressor. Subsection 5.2 defines functions used in the encoding process, and 5.3 specifies the calculation of the output vector from the input vector and compressor parameters.

As specified in 5.3, at any time, |t|, the encoder output, is a variable-length binary vector, |v_o t|, that is a concatenation of three variable-length binary vectors, | vh t|, |vq t|, and |vu t| described below.

The first binary vector, |vh t|, encodes information about recent mask changes (see 5.3.3.1). The most recent change vector is ORed with previous change vectors (to provide robustness against packet loss), and the result is run-length encoded. Next, the effective robustness level, |vV t|, is encoded using 4 bits, followed by information on the mask values for each change. This is followed by the value of |vc t|, which indicates if |dotp v| was set to one more than once in the period covering this cycle and the previous |vV t| cycles. This information is used in the encoding. The final bit indicates whether user-specified parameters |dotf t|and |dotr t| are both zero. If so, the values of those parameters are not encoded in |vq t| or |vu t|.

The second binary vector, |vq t|, encodes information about the entire mask (see 5.3.3.2).
Although mask changes alone would be sufficient to reconstruct the mask, the option to send the entire mask can be requested by setting the send mask flag, |dotf t|, to one (see 3.3.2). In this case, |vq t| consists of a $'1'$ concatenated with the mask that has been preprocessed and run-length encoded.

Finally, the third binary vector, |vu t|, encodes different information depending on the values of |dotr t| and |vc t|. If |dotr t| is one (see 3.3.2), then |vu t| always contains a bit string that encodes the value of the input block length F, followed by the input vector. Otherwise, if |vc t| is one, then |vu t| contains the unpredictable bit values and the values of any bits that changed from unpredictable to predicable in the present change vector or the previous |vV t| change vectors. If |vc t| is not one, then |vu t| contains only the unpredictable bit values. In all cases, the output is preceded by |dotr t| if its value was not already specified by the last bit of |vh t|.

\section*{5.2 BASIC ENCODING FUNCTIONS}
 
\subsection*{5.2.1 OVERVIEW}
 
This subsection defines the counter encoding, run-length encoding, and bit extraction
functions used by the encoding procedure specified in Section~5.3.3.
 
\subsection*{5.2.2 COUNTER ENCODING FUNCTION}
 
Given a positive integer $1 \leq A \leq 2^{16} - 1$, the counter encoding function, denoted
$\mathrm{COUNT}(A)$, maps $A$ onto a variable-length binary vector following Table~\ref{tab:counter}.
 
\begin{table}[h!]
\centering
\caption{Counter Encoding Table}
\label{tab:counter}
\begin{tabular}{ll}
\toprule
\textbf{Input integer, $A$} & \textbf{Output vector} \\
\midrule
$A = 1$               & \texttt{0} \\
$2 \leq A \leq 33$    & \texttt{110} $\mathbin{\vert}$ $\mathrm{BIT}_5(A - 2)$ \\
$A \geq 34$           & \texttt{111} $\mathbin{\vert}$ $\mathrm{BIT}_E(A - 2)$ \\
\bottomrule
\end{tabular}
\end{table}
 
\noindent $E$ is calculated as
\begin{equation}
    E = 2\lfloor \log_2(A - 2) + 1 \rfloor - 6. \tag{9}
\end{equation}
 
\noindent\textbf{Note:} The equation above calculates a bit string length consisting of a number
of zeros concatenated with a minimum-length bit string encoding of the integer $(A - 2)$.
As the relationship between the number of preceding zeros and the length of the bit string
encoding $(A - 2)$ is unique, it can be used by the decompressor to parse the output.
 
\subsection*{5.2.3 RUN-LENGTH ENCODING}
 
Given a binary vector $\mathbf{a}$, the run-length encoding of $\mathbf{a}$, denoted
$\mathrm{RLE}(\mathbf{a})$, is a variable-length binary vector defined as
\begin{equation}
    \mathrm{RLE}(\mathbf{a}) = \mathrm{COUNT}(C_0) \mathbin{\vert} \cdots \mathbin{\vert} \mathrm{COUNT}\!\left(C_{H(\mathbf{a})-1}\right) \mathbin{\vert} \texttt{10}, \tag{10}
\end{equation}
where $C_i$ is one more than the number of consecutive \texttt{0} bits preceding the $i$-th \texttt{1} bit in $\mathbf{a}$, starting at the MSB and decreasing.
 
\noindent\textbf{Notes:}
\begin{enumerate}
    \item If the vector $\mathbf{a}$ ends with one or more zeros, they are not explicitly encoded
    via the \textsc{COUNT} function, as they can be inferred from the length of the input vector
    and the number of \texttt{1} bits, $H(\mathbf{a})$.
    \item When vector $\mathbf{a}$ does not contain any \texttt{`1'} bits, the \textsc{COUNT}
    function will yield a \texttt{10} bit string.
    \item Figure~\ref{fig:rle} provides an illustration of the run-to-count encoding.
\end{enumerate}
 
\begin{figure}[h!]
\centering
\( 0001\;000001\;000001\;00001\;0000001\;1001\;0000000000000000 \)
\[
C_0 = 4,\quad C_1 = 6,\quad C_2 = 1,\quad C_3 = 6,\quad C_4 = 5,\quad C_5 = 7,\quad C_{H(\mathbf{a})-1} = 3
\]
\caption{Example of the Run-to-Count Encoding, converting a binary vector $\boldmath\alpha$
into a sequence of integers.}
\label{fig:rle}
\end{figure}
 
\subsection*{5.2.4 BIT EXTRACTION FUNCTION}
 
Given two binary vectors $\mathbf{a}$, $\mathbf{b}$ having the same length, the bit extraction
of $\mathbf{a}$ relative to $\mathbf{b}$, denoted $\mathrm{BE}(\mathbf{a}, \mathbf{b})$, is the
sequence of bits in $\mathbf{a}$ taken from the positions where $\mathbf{b}$ has a \texttt{1} bit.
That is,
\begin{equation}
    \mathrm{BE}(\mathbf{a}, \mathbf{b}) = \dot{a}_{g_{H(\mathbf{b})-1}} \mathbin{\vert} \cdots \mathbin{\vert} \dot{a}_{g_0}, \tag{11}
\end{equation}
where $g_i$ denotes the position of the $i$-th \texttt{1} bit in $\mathbf{b}$, starting from
the MSB.
 
\subsection*{5.3 ENCODING STEP}
 
\subsubsection*{5.3.1 OUTPUT BINARY VECTOR STRUCTURE}
 
The encoder output is comprised of the sequence of variable-length binary output vectors
$\mathbf{o}_0, \mathbf{o}_1, \mathbf{o}_2, \mathbf{o}_3, \ldots$ Each output binary vector
$\mathbf{o}_t$ shall be defined as
\begin{equation}
    \mathbf{o}_t = \mathbf{h}_t \mathbin{\vert} \mathbf{q}_t \mathbin{\vert} \mathbf{u}_t, \tag{12}
\end{equation}
where variable-length binary vectors $\mathbf{h}_t$, $\mathbf{q}_t$, and $\mathbf{u}_t$ are
specified in Sections~5.3.3.1, 5.3.3.2, and 5.3.3.3, respectively.
 
\subsubsection*{5.3.2 INTERMEDIATE CALCULATIONS}
 
\paragraph{5.3.2.1} For $t \geq 0$, $\dot{d}_t$ is defined as
\begin{equation}
    \dot{d}_t = \begin{cases} 1, & \text{if } \dot{f}_t = 0 \text{ and } \dot{r}_t = 0, \\ 0, & \text{otherwise,} \end{cases} \tag{13}
\end{equation}
where $\dot{f}_t$ and $\dot{r}_t$ are defined in Section~3.3.2.
 
\paragraph{5.3.2.2} For $t \geq 0$, $V_t$ is defined as
\begin{equation}
    V_t = \begin{cases} R_t, & \text{if } (t - R_t) \leq 0, \\ R_t + C_t, & \text{otherwise,} \end{cases} \tag{14}
\end{equation}
where $R_t$ is defined in Section~3.3.2, and $C_t$ is the maximum integer where
$C_t \leq \min(t, 15) - R_t$, for which at a given time instant $t$, all
$\mathbf{D}_{t'} = \mathbf{0}$ (see Section~4.2.3) for
$t' \in \{t - R_t - 1,\; t - R_t - 2,\; \ldots,\; t - R_t - C_t\}$.
 
\noindent\textbf{Note:} $C_t$ counts the number of consecutive occurrences of no mask changes,
starting from the first cycle not covered by the minimum required effective robustness level
and working backwards in time.
 
\subsubsection*{5.3.3 OUTPUT VECTOR COMPONENTS}
 
\paragraph{5.3.3.1} The binary vector $\mathbf{h}_t$ is defined as
\begin{equation}
    \mathbf{h}_t = \mathrm{RLE}(\mathbf{X}_t) \mathbin{\vert} \mathrm{BIT}_4(V_t) \mathbin{\vert} \mathbf{e}_t \mathbin{\vert} \mathbf{k}_t \mathbin{\vert} \mathbf{c}_t \mathbin{\vert} \dot{d}_t, \tag{15}
\end{equation}
where $V_t$ is defined in Section~5.3.2.2, $\dot{d}_t$ is defined in Section~5.3.2.1, and
$\mathbf{X}_t$, $\mathbf{e}_t$, $\mathbf{c}_t$, and $\mathbf{k}_t$ are defined as follows.
 
\begin{equation}
    \mathbf{X}_t = \begin{cases}
        \langle \mathbf{D}_t \rangle, & \text{if } R_t = 0, \\
        \langle \mathbf{D}_1 \;\mathrm{OR}\; \mathbf{D}_2 \;\mathrm{OR}\; \cdots \;\mathrm{OR}\; \mathbf{D}_t \rangle, & \text{if } (t - R_t) \leq 0, \\
        \langle \mathbf{D}_{t-R_t} \;\mathrm{OR}\; \mathbf{D}_{t-R_t+1} \;\mathrm{OR}\; \cdots \;\mathrm{OR}\; \mathbf{D}_t \rangle, & \text{otherwise,}
    \end{cases} \tag{16}
\end{equation}
where $\mathbf{D}_t$ is the change binary vector defined in Section~4.2.3, and $R_t$ is defined in
Section~3.3.2.
 
\begin{equation}
    \mathbf{y}_t = \mathrm{BE}(\langle \neg\mathbf{M}_t \rangle,\; \mathbf{X}_t), \tag{17}
\end{equation}
 
\begin{equation}
    \mathbf{e}_t = \begin{cases}
        \emptyset, & \text{if } V_t = 0 \text{ or } \mathbf{X}_t = \mathbf{0}, \\
        	\texttt{0}, & \text{if } \mathbf{y}_t = \mathbf{0} \text{ and } V_t > 0 \text{ and } \mathbf{X}_t \neq \mathbf{0}, \\
        	\texttt{1}, & \text{otherwise,}
    \end{cases} \tag{18}
\end{equation}
 
\begin{equation}
    \mathbf{k}_t = \begin{cases}
        \emptyset, & \text{if } V_t = 0 \text{ or } \mathbf{X}_t = \mathbf{0} \text{ or } \mathbf{y}_t = \mathbf{0}, \\
        \mathbf{y}_t, & \text{otherwise,}
    \end{cases} \tag{19}
\end{equation}
 
\begin{equation}
    \mathbf{c}_t = \begin{cases}
        \emptyset, & \text{if } \mathbf{k}_t = \emptyset, \\
        	\texttt{0}, & \text{if } \mathbf{k}_t \neq \emptyset \text{ and } \dot{p}_i \text{ is not set to one more than once,} \\
                      & \quad \text{for } i \in \{\max(0, t-V_t),\; \max(0, t-V_t)+1,\; \ldots,\; t-1,\; t\}, \\
        	\texttt{1}, & \text{otherwise.}
    \end{cases} \tag{20}
\end{equation}
 
\paragraph{5.3.3.2} The binary vector $\mathbf{q}_t$ is defined as
\begin{equation}
    \mathbf{q}_t = \begin{cases}
        \emptyset, & \text{if } \dot{d}_t = 1, \\
        	\texttt{1} \mathbin{\vert} \mathrm{RLE}\!\left(\langle \mathbf{M}_t \;\mathrm{XOR}\; (\mathbf{M}_t \!\ll\!) \rangle\right), & \text{if } \dot{f}_t = 1, \\
        	\texttt{0}, & \text{otherwise,}
    \end{cases} \tag{21}
\end{equation}
where $\dot{f}_t$ is defined in Section~3.3.2, and $\dot{d}_t$ is defined in Section~5.3.2.1.
 
\paragraph{5.3.3.3} The binary vector $\mathbf{u}_t$ is defined as
\begin{equation}
    \mathbf{u}_t = \begin{cases}
        \mathrm{BE}\!\left(\mathbf{I}_t,\; (\langle \mathbf{X}_t \rangle \;\mathrm{OR}\; \mathbf{M}_t)\right), & \text{if } \dot{d}_t = 1 \text{ and } \mathbf{c}_t \neq \texttt{1}, \\
        \mathrm{BE}(\mathbf{I}_t,\; \mathbf{M}_t), & \text{if } \dot{r}_t = 1, \\
        	\texttt{1} \mathbin{\vert} \mathrm{COUNT}(F) \mathbin{\vert} \mathbf{I}_t, & \text{if } \dot{r}_t = 1, \\
        	\texttt{0} \mathbin{\vert} \mathrm{BE}\!\left(\mathbf{I}_t,\; (\langle \mathbf{X}_t \rangle \;\mathrm{OR}\; \mathbf{M}_t)\right), & \text{if } \dot{r}_t = 0 \text{ and } \dot{f}_t = 1 \text{ and } \mathbf{c}_t = \texttt{1}, \\
        	\texttt{0} \mathbin{\vert} \mathrm{BE}(\mathbf{I}_t,\; \mathbf{M}_t), & \text{otherwise,}
    \end{cases} \tag{22}
\end{equation}
where $\dot{r}_t$ and $\dot{f}_t$ are defined in Section~3.3.2, $\mathbf{c}_t$ is defined in
Section~5.3.3.1, and $\dot{d}_t$ is defined in Section~5.3.2.1.

\part{Haskell Code}

\section{Data Types} % Types.hs

\subsection*{Section 3.2 Input}
The most basic data type is 
\begin{code}
type Bit = Int
\end{code}
The main data types are the input vector to be compressed,
\begin{code}
type I = [Bit] 
\end{code}
the compressed output vector,
\begin{code}
type O = [Bit]
\end{code}
and the state:
\begin{code}
type S = (I, B, M, [D], Len, Param)
\end{code}
The state is a tuple of the current input vector, the build vector, the mask vector, a list of change vectors, the length of the input 
vector, and the parameters for the current cycle.

\subsection*{Section 3.3 Parameters}
The initial parameters are composed of the initial mask vector, the minimum required effective robustness level, and flags.
These will be updated in each cycle according to the protocol's specifications, and therefore are included in the state.

Each state carries the input, the three Mask Update vectors,
\begin{code}
type B = [Bit] -- Build vector
type M = [Bit] -- Mask vector
type D = [Bit] -- Change vector
\end{code}
the length of the input,
\begin{code}
type Len = Int
\end{code}
and the parameters for the current round. Respectively, initial mask vector, the minimum required effective robustness level, the new 
mask flag, the uncompressed flag, and the send mask flag are defined as follows:
\begin{code}
data Param = Param {
       maskZero :: [Bit] --M0
     , robustnessLevel :: [Bit] -- Rt (r)
     , newMask :: [Bit] -- pt
     , uncompressed :: [Bit] -- rt
     , sendMask :: [Bit] --ft
     } deriving (Eq, Ord, Show)
\end{code}

The initialization parameters\footnote{Taken from \cite{visionspace}.} are
\begin{code}
initParamEnc = Param 
   (nzeros    32)
        [0, 2, 2, 2, 2, 2, 2, 2]
        [0, 1, 0, 0, 0, 0, 0, 0]
        [0, 1, 1, 1, 0, 0, 0, 0]
        [0, 1, 1, 1, 0, 0, 0, 0]
\end{code}
Because the parameters are updated at the start of each cycle, the first round will not be considered and are all set at 0 to align
with the parameter rotation.

The initial state is:
\begin{code}
initState = ([], [], [], [], 32, initParamEnc)
\end{code}
Used in verifying if there will be a new mask:
\begin{code}
type QtMask = Maybe M
\end{code}

\begin{code}
type V = Bit
type X = [Bit]
type Y = [Bit]
type E = [Bit]
type K = [Bit]
type C = [Bit]
\end{code}

\section{ENCODER} % Encoder.hs}
The encoder has type
\begin{code}
encoder :: [I] -> (S, [O])
\end{code}
and is defined by
\begin{code}
encoder = stream_proc gEnc fEnc initState
\end{code}
where
\begin{code}
stream_proc g f = mapAccumL (curry (mealy (uncurry g) (uncurry f)))
\end{code}
is the corresponding map-accumulate process.
Its two parameters |gEnc| and |fEnc| define a Mealy machine:
\footnote{
Note concerning naming, recalling Fig.~\ref{fig:mealy2}: |g|-functions have to do with updating the state while |f|-functions have to do with the production of 
output.}
\begin{itemize}
\item	
	|gEnc :: S -> I -> S| --- updates the state
\item	
	|fEnc :: S -> I -> O| --- produces the output vector
\end{itemize}
Thus |mapAccumL| iterates such a Mealy machine as much as required by the input stream.

The state update goes as follows (see Fig.~\ref{fig:gEnc}, details in the sequel):
\begin{code}
gEnc :: S -> I -> S
gEnc (is, b, m, d, len, param) i = (i, b', m', d': d, len, param')
   where
        b' = gB i s 
        m' = gM i s
        d' = gD m' s
        s = (is, b, m, d, len, param')
        param' = next param
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=1\textwidth]{images/gEnc.png}
  \caption{Encoder state update function |gEnc|.}
  \label{fig:gEnc}
\end{figure}
The output vector is produced as follows (per section 5.3.1, details in the sequel):
\begin{code}
fEnc :: S -> I -> O
fEnc s i = newH ++ newQ ++ newU where
        newH = fH x v e k c ddot
        newQ = fQ s ddot
        newU = fU i s x c ddot
        x = vecX s
        v = funcV s
        e = vecE y x v
        k = vecK v x y
        c = vecC k v s
        ddot = funcD s
        y = vecY s x
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=1\textwidth]{images/fEnc.png}
  \caption{fEnc}
  \label{fig:fEnc}
\end{figure}

\subsection*{Section 4.2 Mask Update}

The state update by |gEnc| is factored over three functions, each handling the corrresponding component of the state,
namely:
\subsubsection*{Section 4.2.1}
The build,
\begin{code}
gB :: I -> S -> B
gB i ([], b, _, _, _, param) = zeros (maskZero param)
gB i (i', b, _, _, _, param) = if a == 0 then  kern i i' b else zeros b
                        where (a:_) = newMask param
\end{code}
\subsubsection*{Section 4.2.2}
The mask,
\begin{code}
gM :: I -> S -> M
gM i ([], _, _, _, _, param) = maskZero param 
gM i (i', b, m, _, _, param) = kern i i' (if a == 0 then m else b)
                            where 
                                (a:_) = newMask param
\end{code}
\subsubsection*{Section 4.2.3}
The change:
\begin{code}
gD :: M -> S -> D
gD m1 ([], _, m, [], _, _) = zeros m1
gD m1 (_, _, m, _, _, _) = unpredict m1 m

\end{code}
The followig function captures de essence ('kernel') of the update process:
\begin{code}
kern :: Bits d => [d] -> [d] -> [d] -> [d]
kern = zipWith3 g where g i j b = (i `xor` j) .|. b
\end{code}

\subsection*{Section 5.3.3 Output Vector Components}

Concerning |fEnc|, the output vector is produced by
\subsubsection*{Section 5.3.3.1}
\begin{code}
fH :: X -> Bit -> E -> K -> C -> Bit -> [Bit]
fH x v e k c ddot = rle x ++ toNBits 4 v ++ e ++ k ++ c ++ [ddot]
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=0.7\textwidth]{images/fH.png}
  \caption{fH}
  \label{fig:fH}
\end{figure}

together with
\subsubsection*{Section 5.3.3.2}
\begin{code}
fQ :: S -> Bit -> [Bit]
fQ (_, _, m, _, _, param) ddot
       | ddot == 1 = []
       | sm == 1 = 1 : rle (reverse (undpcm m))
       | otherwise = [0]
       where 
          (sm:_) = sendMask param
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=0.7\textwidth]{images/fQ.png}
  \caption{fQ}
  \label{fig:fQ}
\end{figure}

and
\subsubsection*{Section 5.3.3.3}
\begin{code}
fU :: I -> S -> X -> C -> Bit -> [Bit]
fU i (_, _, m, _, _, param) x c ddot
       | ddot == 1 && c == [1] = f y
       | ddot == 1 && c /= [1] = f m
       | uncpr == 1 = 1 : count (length i) ++ i
       | uncpr == 0 && sm == 1 && ch == 1 = 0 : f y
       | otherwise = 0 : f m 
       where
           y = zipWith (.|.) (reverse x) m
           (ch:_) = c
           (uncpr:_) = uncompressed param
           (sm:_) = sendMask param
           f = reverse . (be i)
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=0.7\textwidth]{images/fU.png}
  \caption{fU}
  \label{fig:fU}
\end{figure}

\subsection*{Section 5.2.4 Bit Extraction Function}
The following function, used above, is such that |be x m| keeps the |a|s in |x| that match the 'mask' |vM()|:
\begin{spec}
be :: [a] -> [Bit] -> [a]
be [] _ = []
be _ [] = []
be (x:a) (1:b) = x:be a b
be (_:a) (0:b) =   be a b
\end{spec}
A version better for calculations is:
\begin{code}
be :: [a] -> [Bit] -> [a]
be = fmap f . zip where f = map fst . filter ((/=0).snd) 
\end{code}

\subsection*{Section 5.3.2 Intermediate calculations}
The following intermediate calculations are used in the production of the output vector, and are defined as follows.
\subsubsection*{Section 5.3.2.1}
\begin{code}
funcD :: S -> Bit
funcD (_, _, _, _, _, param)
       | (sm == 0 && uncpr == 0) = 1
       | otherwise = 0
       where (sm:_) = sendMask param
             (uncpr:_) = uncompressed param
\end{code}
\subsubsection*{Section 5.3.2.2}
\begin{code}
funcV :: S -> Bit
funcV (_, _, _, ds, _, param)
       | t <= rl   = rl
       | otherwise = rl + ct
       where
          (rl:_) = robustnessLevel param
          t      = length ds - 1
          upper  = min t 15
          x  = take (upper - rl) (drop (rl + 1) ds)
          y  = takeWhile (all (==0)) x
          ct = length y
\end{code}

\subsubsection*{Section 5.3.3.1}
For the first output sub-vector, a vector |x| is defined as the OR of the change vectors in the period covering the current cycle and 
the previous |vV t| cycles
\begin{code}
vecX :: S -> X
vecX  = reverse . aux 
  where 
      aux (_, _, _, ds, _, param)
        | rl == 0 = d
        | tl - rl <= 0 = foldl1 l ds
        | otherwise = foldl1 l dt
        where
          (d:restD) = ds 
          tl = length ds - 1
          (rl:_) = robustnessLevel param
          dt = take (rl + 1) ds
          l = zipWith (.|.)
\end{code}
which is concatenated with the following functions for the calculation of the |h|-component of the output vector,
\begin{code}
vecY :: S -> X -> Y
vecY (_, _, m, _, _, _) x =  be x (reverse (bitflip m)) 
    where
        bitflip = map (1-)
\end{code}
\begin{code}
vecE :: Y -> X -> V -> E
vecE y x v
       | v == 0 || x == zeros x = []
       | y == zeros y && v > 0 && x /= zeros x = [0] 
       | otherwise = [1]
\end{code}
\begin{code}
vecK :: V -> X -> Y -> K
vecK v x y
      | v == 0 || x == zeros x || y == zeros y = []
      | otherwise = y
\end{code}
\begin{code}
vecC :: K -> V -> S -> C
vecC [] _ _ = []
vecC k v (_, _, _, ds, _, param)
           | sum(is) > 1 = [0]
           | otherwise = [1]
           where
                 t = length ds - 1
                 is = [(max 0 (t-v)) .. t]
\end{code}

\section{DECODER} % Decoder.hs}
The decoder has type:
\begin{spec}
decoder :: [O] -> (S, [I])
\end{spec}
We are currently only implementing forward decoding.
The state is kept the same as the |encoder|'s.
\begin{spec}
type S = ([I], B, M, [D], Len, Param)
\end{spec}
|vB()| stays empty in decoding. Then:
\begin{code}
decoder :: [O] -> (S, [I])
decoder = stream_proc gDec fDec initState
    where
        initState = ([], [], [], [], 0, initParamDec)
\end{code}
The order is: mask, robustness level, new mask, uncompressed flag, send mask flag.
All are initialized to |null| for decoding, as we will reconstruct them from the encoded input:
\begin{code}
initParamDec = Param [] [] [] [] []
\end{code}

|gDec| consumes previous state and current encoded input, yielding next state.
\begin{code}
gDec :: S -> O -> S
gDec (itPrev, _, m, ds, len, param) o = (it, [], newM, newD : ds, newLen, newParam)
    where 
        (dx, dv, de, dk, dc, ddot, qtMask, fBit, utBits) = decodeParts o
        rBit      = if ddot == 0 && not (null utBits) then head utBits else 0
        newLen    = if rBit == 1 then getInputLen (drop 1 utBits) else len
        m'        = if null m then nzeros newLen else m
        mtFromH   = updateM m' dx dv de dk
        newM      = maybe mtFromH id qtMask
        newD      = nzeros (newLen - length dx) ++ reverse dx   
        newParam  = param
            { sendMask     = fBit : sendMask param
            , uncompressed = rBit : uncompressed param
            }
        it = decodeU ddot dc fBit newM dx itPrev utBits
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=1\textwidth]{images/gDec.png}
  \caption{gDec}
  \label{fig:gDec}
\end{figure}

|fDec| consumes the new state and current encoded input, yielding its reconstruction.
\begin{code}
fDec :: S -> O -> I 
fDec (itPrev, _, _, _, _, _) o = itPrev
\end{code}

\subsection*{Section 5.3.3 Output Vector Components}
|decodeParts| parses the |h|-component of the encoded output and checks the |q|-component to possibly return the new mask.
\begin{code}
decodeParts :: O -> (X, Bit, E, K, C, Bit, QtMask, Bit, [Bit])
decodeParts o = (dx, dv, de, dk, dc, ddot, qtMask, fBit, utBits)
    where
        (dx, dv, de, dk, dc, ddot, restBits) = decodeH o
        (qtMask, fBit, utBits)               = checkMask ddot restBits
\end{code}

\subsubsection*{Section 5.3.3.1}
|decodeH| is a bit-string parser implemented below using a simple state-monad:
\begin{code}
decodeH :: [Bit] -> (X, Bit, E, K, C, Bit, [Bit])
decodeH = runST g where
    g = do { dx <- St(decodeXt);
             x  <- St(nspan 4);
             let dv = fromBinary x
             in do { de   <- St(decodeE dx dv);
                     dk   <- St(decodeK dx de);
                     dc   <- St(decodeC dk);
                     ddot <- St(nspan 1);
                     rest <- get;
                     return (dx,dv,de,dk,dc,head ddot,rest)
                    }
           }
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=0.7\textwidth]{images/decodeH.png}
  \caption{decodeH}
  \label{fig:decodeH}
\end{figure}
To decode each component of |h|,
\begin{code}
decodeXt ot = (dx, otp) where
    dx = unrle ot 0
    otp = drop b ot
    b = length (rle dx)
\end{code}
\begin{code}
decodeE :: X -> Bit -> [Bit] -> (E, [Bit])
decodeE dx dv otp = nspan (if dx == [] || dv == 0  then 0 else 1) otp
\end{code}
\begin{code}
decodeK :: X -> E -> [Bit] -> (K, [Bit])
decodeK dx de otp = nspan (if de == [1] then length dx else 0) otp
\end{code}
\begin{code}
decodeC :: K -> [Bit] -> (C, [Bit])
decodeC dk otp = nspan (if null dk then 0 else 1) otp
\end{code}

\subsubsection*{Section 5.3.3.2}

The next step is to verify if there will be a new mask
\begin{code}
checkMask :: Bit -> [Bit] -> (QtMask, Bit, [Bit])
checkMask 1 bits = (Nothing, 0, bits)
checkMask _ [] = (Nothing, 0, [])
checkMask _ (0:rest) = (Nothing, 0, rest)
checkMask ddot (f:rest) =
    let (qtPayload, utBits) = splitPayload rest
        fullMask            = decodeQ (f : qtPayload) ddot
    in (Just fullMask, f, utBits)
\end{code}
which will be calculated by
\begin{code}
decodeQ :: [Bit] -> Bit -> [Bit]
decodeQ bits ddot
        | ddot == 1 = bits
        | f == 0 = tail bits -- if f = 0, no more info
        | otherwise = undpcm (reverse (unrle (tail bits) 0))
        where
                f = head bits
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=0.7\textwidth]{images/decodeQ.png}
  \caption{decodeQ}
  \label{fig:decodeQ}
\end{figure}

\noindent In the first case, the vector only exists if |ddot = 0|. Otherwise, the full mask is the RLE of the reverse of the XOR of |M| and 
left-shifted |M|, so we need to reverse and |undpcm| to get the full mask.
\begin{code}
undpcm :: [Bit] -> [Bit]
undpcm [] = []
undpcm [x] = [x]
undpcm (x:y:xs) = (x `xor` y) : undpcm (y:xs)
\end{code}

This vector does not always encode the full mask, as it is activated by a user-specified flag.
With the information obtained from the decoding of the |h|-component, we can update the mask as follows in the case of no mask 
encoded by |q|:
\begin{code}
updateM :: M -> X -> Bit -> E -> K -> M
updateM mt dx dv de dk
    | dx == []  = mt
    | dv == 0   = unpredict mt rdx
    | de == [0] = zipWith (\m dv -> if dv == 1 then 1 else m) mt rdx
    | de == [1] = fst (mapAccumL aux dk (zip mt rdx))
    where
        rdx = nzeros (length mt - length dx) ++ reverse dx -- pad to mask length
        aux acc (m, 0) = (acc, m)
        aux (k:ks) (m, 1) = (ks, 1 - k)
        aux [] (m, 1) = ([], m)
\end{code}

\subsubsection*{Section 5.3.3.3}
Finally, to recover the input, we need to reconstruct the compression cases defined by |fU|.
\begin{code}
decodeU :: Bit -> C -> Bit -> M -> X -> I -> [Bit] -> [Bit]
decodeU dt ct f_t mt xt itPrev utBits
    | dt == 1   = decodeDt1 ct mt xt itPrev utBits
    | otherwise = decodeDt0 f_t ct mt xt itPrev utBits
\end{code}
\begin{figure}%[H]
  \centering
  \includegraphics[width=0.7\textwidth]{images/decodeU.png}
  \caption{decodeU}
  \label{fig:decodeU}
\end{figure}
select mask for |ddot = 1|
\begin{code}
maskDt1 :: C -> X -> M -> M
maskDt1 [1] xt mt = zipWith (.|.) (reverse xt) mt
maskDt1 _ _  mt = mt

\end{code}
Case 1 and 2: |ddot = 1|
\begin{code}
decodeDt1 :: C -> M -> X -> I -> [Bit] -> [Bit]
decodeDt1 ct mt xt itPrev ut = 
    let mask = maskDt1 ct xt mt
        bs = reverse (take (sum mask) ut)
    in patch itPrev mask bs

\end{code}
select mask for |ddot = 0|
\begin{code}
maskDt0 :: Bit -> C -> X -> M -> M
maskDt0 1 [1] xt mt = zipWith (.|.) (reverse xt) mt
maskDt0 _ _     _  mt = mt

\end{code}
Case 3, 4 and 5: |ddot = 0|
\begin{code}
decodeDt0 :: Bit -> C -> X -> M -> I -> [Bit] -> [Bit]
decodeDt0 _ ct xt mt itPrev bits@(1:rest) = -- Case 3, Uncompressed (r == 1)
    let f            = getInputLen rest
        payload      = drop (length (count f)) rest
        (it, rest')  = splitAt f payload
    in it
\end{code}
Case 4 and 5: Compressed (|r == 0|)
\begin{code}
decodeDt0 f_t ct xt mt itPrev (0:rest) = -- Case 4 and 5: Compressed (r == 0)
    let mask = maskDt0 f_t ct xt mt
        bs = reverse (take (sum mask) rest)
    in 0 : patch itPrev mask bs 
\end{code}

To get the length of the input in case of uncompressed input, we use:
\begin{code}
getInputLen :: [Bit] -> Int
getInputLen bits = head (uncounting bits)
\end{code}
 
Function to split bits for |vq()| and |vu()|:
\begin{code}
splitPayload :: [Bit] -> ([Bit], [Bit])
splitPayload [] = ([], [])
splitPayload [x] = ([x], [])
splitPayload (1:0:xs) = ([1,0], xs)
splitPayload (x:xs) =
        let (qt, ut) = splitPayload xs
        in (x : qt, ut)
\end{code}

\section{RLE}
\subsection*{Section 5.2.3 Run-Length Encoding}
RLE encoding:
\begin{code}
rle :: [Bit] -> [Bit]
rle = counting . init . map (+1) . map length . splitOn [1]
\end{code}
RLE decoding:
\begin{code}
unrle :: [Bit] -> Int -> [Bit] 
unrle = flip pipeline where
      pipeline n = intercalate [1] . map (flip replicate 0) . map (subtract 1) . trail n . uncounting 
      trail n s = s ++ [n - (sum s + length s)]
\end{code}
\subsection*{Section 5.2.2 Counter Encoding Function}
Counting:
\begin{minip}{eq:counting}
\begin{code}
counting :: [Int] -> [Bit]
counting = cataList cGen
\end{code}
where
\begin{code}
cGen :: Either () (Int, [Bit]) -> [Bit]
cGen = either l r where
       l = inj10 . nil
       r = conc . (count >< id) 
\end{code}

\end{minip}
The |count| function:
\begin{spec}
count :: Int -> [Bit]
count 1 = inj0 []
count a
    | a >= 2 && a <= 33 = inj110 (toNBits 5 (a-2))
    | otherwise         = inj111 (toNBits (e a) (a-2))
\end{spec}
The 'E' function:
\begin{minip}{eq:E}
\begin{code}
e :: Int -> Int
e a = 2 * (floor (logBase 2 a' + 1)) - 6
      where a' = fromIntegral (a - 2)
\end{code}
\end{minip}
NB: the following (simpler) alternative is used instead:
\begin{minip}{eq:count}
\begin{code}
count :: Int -> [Bit]
count = either (inj0 . nil) g2 . outNat . pred
  where
  g2 a
    | a >= 0 && a <= 31 = inj110 (toNBits 5     a)
    | otherwise         = inj111 (toNBits (e a) a)
  e    a = 2*(minb a) - 6
  minb a = floor (logBase 2 ((fromIntegral a)) + 1)
\end{code}
\end{minip} 
Injections:
\begin{minip}{eq:injs}
\begin{code}
inj0 = ([0]++)
inj10 = ([1,0]++)
inj110 = ([1,1,0] ++)
inj111 = ([1,1,1] ++)
\end{code}
\end{minip}
Uncounting:
\begin{minip}{eq:uncounting}
\begin{code}
uncounting :: [Bit] -> [Int]
uncounting = unfoldr parse
\end{code}
\end{minip}
where the bit vector 'parsing gene' is:
\begin{minip}{eq:parse}
\begin{code}
parse [1,0] = Nothing
parse (0:r) = Just(1,r)
parse (1:(1:(0:r))) = Just(fromBinary a + 2, r')
    where (a,r') = nspan 5 r
parse (1:(1:(1:r))) = Just (fromBinary a + 2, r')
    where (a, r') = nspan (6 + length x) r'' ; (x, r'') = cspan (==0) r
parse _ = Nothing
\end{code}
\end{minip}

\section{pocket.hs}
To test the encoder and decoder, we use the following test vectors, taken from the reference implementation in C++. 
The |bits| vector is the input to be compressed, |compressed| is the output of the encoder, and |decompressed| is the output of the 
decoder, which should match |bits|.
\begin{code}
bits :: [[Bit]]
bits = [[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1],[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1],[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1],[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,1,0],[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,1,0],[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,1,0],[1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,1,0,1,1,1,0,1,0,0,1]]
compressed :: [[Bit]]
compressed = [[1,0,0,0,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1],[1,0,0,0,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1],[1,0,0,0,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1],[0,0,1,0,0,0,1,1,0,1,0,1],[0,0,1,0,0,1,0,0,0,1,0,1],[0,0,1,0,0,1,0,1,0,1,0,1],[1,1,0,0,0,0,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1,1,0,0,1,0,1,1,0,1]]
decompressed :: [[Bit]]
decompressed = bits
\end{code}

The test can be done automatically with:
\begin{code}
testEncoder :: Bool
testEncoder = compressed == snd(encoder bits)

testDecoder :: Bool
testDecoder = decompressed == snd(decoder compressed)
\end{code}

\subsection*{ENCODER : Testing specific states and inputs}
We can also test specific states and inputs, to verify the intermediate calculations and outputs of the encoder.
To do this, we define each state and output vector separately, as follows.
\begin{code}
i0 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1] 
i1 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1]        
i2 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1] 
i3 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,1,0]
i4 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,1,0]
i5 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,1,0]
i6 = [1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,1,0,1,1,1,0,1,0,0,1]

sie = ([],[],[],[], 32, initParamEnc)

s0e = gEnc sie i0
e0 = fEnc s0e i0

s1e = gEnc s0e i1
e1 = fEnc s1e i1

s2e = gEnc s1e i2
e2 = fEnc s2e i2

s3e = gEnc s2e i3
e3 = fEnc s3e i3

s4e = gEnc s3e i4
e4 = fEnc s4e i4

s5e = gEnc s4e i5
e5 = fEnc s5e i5

s6e = gEnc s5e i6
e6 = fEnc s6e i6

\end{code}

\subsection*{DECODER : Testing specific states and inputs}
To  test specific states and inputs for the decoder, we can use the same states as for the encoder, but now as input to the decoder, 
and the output should match the input of the encoder.
\begin{code}
o0 = [1,0,0,0,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1]
o1 = [1,0,0,0,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1]
o2 = [1,0,0,0,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,0,0,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1]
o3 = [0,0,1,0,0,0,1,1,0,1,0,1]
o4 = [0,0,1,0,0,1,0,0,0,1,0,1]
o5 = [0,0,1,0,0,1,0,1,0,1,0,1]
o6 = [1,1,0,0,0,0,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1,1,0,0,1,0,1,1,0,1]

sid = ([],[],[],[], 0, initParamDec)

s0d = gDec sid o0
d0 = fDec s0d o0

s1d = gDec s0d o1
d1 = fDec s1d o1

s2d = gDec s1d o2
d2 = fDec s2d o2

s3d = gDec s2d o3
d3 = fDec s3d o3

s4d = gDec s3d o4
d4 = fDec s4d o4

s5d = gDec s4d o5
d5 = fDec s5d o5

s6d = gDec s5d o6
d6 = fDec s6d o6
\end{code}

\section{Auxiliary functions} % Helpers.hs}
The making of a Mealy machine:\footnote{Note how |g| updates the state before |f| yields the output.}
\begin{code}
mealy :: ((s, i) -> s) -> ((s, i) -> o) -> (s, i) -> (s, o)
mealy g f = (split fst f) . (split g snd)
\end{code}
Generating |0|-vectors:
\begin{code}
zeros = map (const 0)
nzeros n = replicate n 0
\end{code}
Bit (un)predictability:
\begin{code}
unpredict = zipWith xor 
\end{code}
Encode positive integer in specified number of bits:\footnote{Cf.\ the alternative |toNBits e = reverse . take e . unfoldr (Just . swap . flip divMod 2)|. }
\begin{code}
toNBits :: Int -> Int -> [Bit]
toNBits n x = nzeros (n - length bits) ++ bits
  where
    bits = toBinary x 
\end{code}
Converse of |toNBits|:
\begin{code}
fromNBits :: Int -> [Bit] -> Int
fromNBits _ = fromBinary
\end{code}
Auxiliary, for non-negative integers:
\begin{code}
toBinary :: Int -> [Bit]
toBinary 0 = [0]
toBinary x = reverse (helper x)
  where
    helper 0 = []
    helper y = (y `mod` 2) : helper (y `div` 2)
\end{code}
Note the post-condition:
\begin{eqnarray}
	|x > 0 => length (toBinary x) = floor(logBase 2 x) + 1|.
\end{eqnarray}
Converse of |toBinary|:
\begin{code}
fromBinary :: [Bit] -> Int
fromBinary = foldl (\acc b -> acc * 2 + b) 0
\end{code}
Parameter rotation:
\begin{code}
next :: Param -> Param
next (Param m nm rl u s) = Param m (rot nm) (rot rl) (rot u) (rot s)
  where rot (h:t) = t ++ [h] -- non-empty list rotation
\end{code}
Auxiliary function to patch the recovered input:
\begin{code}
patch :: I -> M -> [Bit] -> I
patch [] _ _ = []
patch (p:ps) [] _ = p : ps
patch (p:ps) (m:ms) [] = p : patch ps ms []
patch (p:ps) (m:ms) (b:bs)
  | m == 1    = b : patch ps ms bs  
  | otherwise = p : patch ps ms (b:bs)
\end{code}
Span on count:
\begin{minip}{eq:nspan}
\begin{code}
nspan n = split (take n) (drop n) 
\end{code}
\end{minip}
Span on condition:
\begin{minip}{eq:cspan}
\begin{code}
cspan p = split (takeWhile p) (dropWhile p)
\end{code}
\end{minip}

\section{Basic properties}
Let us define
\begin{eqnarray}
\start
	|ln    n = (==n).length|
\more
	|ceil n = (ins {0..n-1})|
\end{eqnarray}
Then |toNBits n| has relational type |(ceil (pw n)) -> (ln n)|, that is,
\begin{eqnarray}
	|toNBits n . crflx (ceil (pw n)) atmost (crflx (ln n)) . toNBits n|
\end{eqnarray}
Moreover, we have the following basic properties:
\begin{eqnarray}
\start
	|fromBinary . toNBits n = id|
	\label{eq:260604d}
\more 
	|length . (flip replicate a) = id|
\more
	|intercalate a (splitOn a x) = x|
\more
	|(subtract 1) . (+1) = id|
\more
	|init (trail n xs) = xs|
\end{eqnarray}

Despite the functions not always being direct inverses of each other, these properties are enough to show that 
|unrle . rle = id|, as the pipeline of |rle| can now be inverted step by step.

It remains to verify the properties of |count| and |uncounting|. We will get to them in the next section.

From the associative property of concatenation, |a ++ (b ++ c) = (a ++ b) ++ c|, for |inj| any of the injections of (\ref{eq:injs}), we have
\begin{eqnarray}
	|conc . (inj >< id) = inj . conc|
	\label{eq:260603a}
\end{eqnarray}
Concerning |conc|, |nspan| (\ref{eq:nspan}) and |cspan|: 
\begin{eqnarray}
\start | conc . nspan n = id |
\more  | conc . cspan p = id |
\more  | uncurry nspan . split (length.p1) conc = id|	\label{eq:260604a}
\end{eqnarray}
Property (\ref{eq:260604a}) says that |length . p1| is a least complement of |conc|. Another way to  say the same is:
\begin{eqnarray}
	|nspan n . conc . (crflx (ln n) >< id) atmost id|
	\label{eq:260604b}
\end{eqnarray}

\section{Correctness argument details}

To assist the correctness, the follwing rules of relation algebra \cite{pdbc}  will be used:
\begin{eqnarray}
\textbf{Involution}                         & |conv2 R = R|   \label{eq:involution} \\
\textbf{Contravariance}                     & |conv ((R . S)) = conv S . conv R|   \label{eq:contrav} \\
\textbf{Shunting Rules}                     & |R . conv f atmost S equiv R atmost S . f| \label{eq:shuntingR} \\
                                            & |f . R atmost S equiv R atmost (conv f) . S| \label{eq:shuntingL} \\
\textbf{Relation Union Universal property}  & |cup R S atmost X equiv R atmost X| \wedge |S atmost X| \label{eq:univprop} \\
\textbf{Relation Union Right Linearity}     & |R . ((cup S Q)) = cup (R . S) (R . Q)| \label{eq:distributivity} \\
\textbf{Converse-$\cup$}                    & |conv ((cup R S)) = cup (conv R) (conv S)| \label{eq:convunion} \\
\textbf{Converse-coreflexive}               & |conv (Phi p) = Phi p|   \label{eq:convcore} \\
\textbf{Guards}                             & |p? = conv [Phi p , Phi (neg p)]|   \label{eq:guards} \\
\textbf{McCarthy conditional}               & |p rArrow R,S = [R,S] . p?|   \label{eq:mccarthy} \\
\textbf{Functor-|><|-composition}           & |(R >< S) . (P >< Q) = (R . P) >< (S . Q)|   \label{eq:functorxcomp} \\
\textbf{Functor-|><|-converse}              & |conv ((R >< S)) = conv R >< conv S| \label{eq:funcxconv} \\
\textbf{Coproduct Definition}               & |either R S = R . cup (conv i1) S . conv i2| \label{eq:copdef} \\
\textbf{+-fusion}                           & |R . (either S Q) = either (R . S)(R . Q)| \label{eq:copfusion} \\
\textbf{Divide and Conquer}                 & |[R,S] . conv [Q,U] = cup ((R . conv Q)) ((S . conv U))| \label{eq:divandconq} \\
\textbf{Extensional Equality}               & |f = g <=>| \langle \forall |x :: f x = g x | \rangle \label{eq:exteq} \\
\textbf{Def-|><|}                           & |(f >< g) (a,b) = (f a, g b)| \label{eq:defx} \\
\textbf{Def-split}                          & |(split f g) x = (f x, g x)| \label{eq:defsplit} \\
\textbf{Cata-cancellation}                  & |cataList alpha = alpha . F (cataList alpha) . out| \label{eq:catacanc}
\end{eqnarray}

\paragraph{Calculation of |uncounting| (\ref{eq:uncounting})}
The strategy is to invert |counting| (\ref{eq:counting}) in order to obtain
|Uncounting| (a relation, in general --- hopefully function (\ref{eq:uncounting}) in the end):
\begin{eqnarray*}
\start
|
	Uncounting = conv counting
|
\just\equiv{ definition of |counting| }
|
	Uncounting = conv (cataList cGen)
|
\just\equiv{ (\ref{eq:catacanc}) ,  (\ref{eq:contrav}), (\ref{eq:involution})}
|
	Uncounting = anaList (conv  cGen)
|
\just\equiv{ let |Parse = conv cGen| --- a non-deterministic parser to begin with }
|
	Uncounting = anaList Parse
|
\end{eqnarray*}

|counting|, a catamorphism, is illustrated in (\ref{eq:cataCGEN}) and |Uncounting|, an anamorphism, is illustrated in (\ref{eq:anaCGEN}).
\begin{eqnarray}
\xymatrix@@C=2cm{
    |Nat0|^*
           \ar[d]_-{|cataList cGen|}
           \ar[r]^-{|outNat|}
&
    |1 + Nat0 >< Nat0|^*
           \ar[d]^-{|id + id >< cataList cGen|}
\\
     |Bit|^*
&
     |1 + Nat0 >< Bit|^*
           \ar[l]^-{|cGen|}
}
\label{eq:cataCGEN}
\end{eqnarray}

\begin{eqnarray}
\xymatrix@@C=2cm{
    |Nat0|^*
&
    |1 + Nat0 >< Nat0|^*
           \ar[l]_-{|inNat|}
\\
     |Bit|^*
           \ar[u]^-{|anaList (conv cGen)|}
           \ar[r]_-{|conv cGen|}
&
     |1 + Nat0 >< Bit|^*
           \ar[u]_-{|id + id >< anaList (conv cGen)|}
}
\label{eq:anaCGEN}
\end{eqnarray}

Unfolding |Parse|:
\begin{eqnarray*}
\start
|
	Parse = conv cGen
|
\just\equiv{ definition of |cGen|; 
             (\ref{eq:copdef}); 
             (\ref{eq:convunion}); 
             (\ref{eq:contrav}) $\times 2$
            }
|
	Parse     = cup (i1 . (conv l))(i2 . conv r)
|
\just\equiv{ definition of |cGen|; 
             (\ref{eq:contrav}) $\times 2$; 
             (\ref{eq:funcxconv}) }
|
	Parse     = cup (
		i1 . conv nil . conv (inj10)
	)(
		i2 . (conv count >< id) .  conv conc
	)
|
\end{eqnarray*}
Inverting |count|:
\begin{eqnarray*}
\start
|
	count = either (inj0 . nil) g2 . outNat . pred
|
\just\equiv{ (\ref{eq:contrav}) $\times 2$ }
|
	conv count = succ . inNat . conv(either (inj0 . nil) g2)
|
\just\equiv{ |inNat = [const 0, succ]|; \ref{eq:copfusion} }
|
	conv count = either (const 1) ((2+)) . conv(either (inj0 . nil) g2)
|
\just\equiv{ \ref{eq:divandconq} }
|
	conv count = cup (const 1 . conv((inj0. nil))) ((2+) . conv g2)
|
\end{eqnarray*}
Abbreviating
\begin{eqnarray}
\start
	|tnb f = uncurry toNBits . split f id|
	\label{eq:tnb}
\more
	|pre = (ceil (pw 5))|
\more
	|post = (ln      5)|
\end{eqnarray}
one has:\footnote{Also note, if needed: |(2+) . crflx pre = crflx post . (2+)| where |post a = a ins [2..33]|.}
\begin{eqnarray*}
\start
|
	g2 = pre -> inj110 . tnb (const 5), inj111 . tnb e
|
\just\equiv{ \ref{eq:mccarthy}; \ref{eq:guards}; \ref{eq:divandconq}; \ref{eq:convcore} }
|
 	g2 = cup (inj110 . (tnb (const 5) . crflx pre)) (inj111 . (tnb e . crflx (not pre)))
|
\just\equiv{ \ref{eq:convunion} ; \ref{eq:contrav} }
|
	conv g2 = cup	(conv ((tnb (const 5). crflx pre)) . conv inj110)
			(conv ((tbn e . crflx (not pre))) . (conv (inj111)))
|
\just\implies{  \ref{eq:distributivity} }
|
	(2+) . conv g2 = cup	((2+) . conv ((tnb (const 5). crflx pre)) . conv inj110)
			((2+) . conv ((tbn e . crflx (not pre))) . (conv (inj111)))
|
\end{eqnarray*}
Putting everything together:
\begin{eqnarray*}
\start
|
	conv count
=
	cup3 (
		const 1 . conv ((inj0 . nil))
	)(
		(2+) . (conv ((tnb (const 5) . crflx pre))) . conv inj110
	)(
		(2+) . (conv ((tnb e         . crflx (not pre)))) . conv inj110
	)
|
\end{eqnarray*}
Moreover ($\cup$-distribution, etc):
\begin{eqnarray*}
\start
|
	i2 .(conv count >< id) . conv conc
|
\just={definition of count; \ref{eq:distributivity}; \ref{eq:contrav}}
|
	cup3 (
		i2 . (const 1 . conv ((inj0 . nil)) >< id) . conv conc
	)(
		i2 . ((2+) . (conv ((tnb (const 5) . crflx pre))) >< id) . conv ((conc . (inj110 >< id)))
	)(
		i2 . ((2+) . (conv ((tnb e         . crflx (not pre)))) >< id) . conv ((conc . (inj111 >< id)))
	)
|
\just={ |id . (id . id) = id|; \ref{eq:functorxcomp}; \ref{eq:contrav}; \ref{eq:involution}; \ref{eq:funcxconv}; |conv id = id|; \ref{eq:260603a} }
|
	cup3 (
		i2 . (const 1 >< id) . conv ((conc . (inj0 >< id) . (nil >< id)))
	)(
		i2 . ((2+) . (conv ((tnb (const 5) . crflx pre))) >< id) . conv ((inj110 . conc))
	)(
		i2 . ((2+) . (conv ((tnb e         . crflx (not pre)))) >< id) . conv ((inj111 . conc))
	)
|
\end{eqnarray*}
Finally:
\begin{eqnarray*}
|
	Parse = cup4 (
		i1 . conv nil . conv (inj10)
	)(
		i2 . (const 1 >< id) . conv ((inj0 . conc . (nil >< id)))
	)(
		i2 . ((2+) . (conv ((tnb (const 5) . crflx pre))) >< id) . conv ((inj110 . conc))
	)(
		i2 . ((2+) . (conv ((tnb e         . crflx (not pre)))) >< id) . conv ((inj111 . conc))
	)
|
\end{eqnarray*}
\paragraph{Calculating |parse|.}
The equality above can be factored into a |atmost|-part and a |atleast|-part.
Let us focus on the latter:
\begin{eqnarray}
\start
|
	cup4 (
		i1 . conv nil . conv (inj10)
	)(
		i2 . (const 1 >< id) . conv ((inj0 . conc . (nil >< id)))
	)(
		i2 . ((2+) . (conv ((tnb (const 5) . crflx pre))) >< id) . conv ((inj110 . conc))
	)(
		i2 . ((2+) . (conv ((tnb e         . crflx (not pre)))) >< id) . conv ((inj111 . conc))
	) atmost Parse
|
	\nonumber
\just\equiv{ \ref{eq:univprop}; \ref{eq:shuntingR}; \ref{eq:contrav}}
|
	lcbr4(
		i1 . conv nil  atmost  Parse . inj10
	)(
		i2 . (const 1 >< id) . conv p2  atmost Parse . inj0
	)(
		i2 . ((2+) . (conv ((tnb (const 5) . crflx pre))) >< id) . conv conc atmost Parse . inj110
	)(
		i2 . ((2+) . (conv ((tnb e         . crflx (not pre)))) >< id) . conv conc atmost Parse . inj111 
	) 
|
	\label{eq:260604c}
\end{eqnarray}
It is already clear that |Parse| is doing 'induction' on the four bit injections (\ref{eq:injs}). Moving on:
\begin{eqnarray*}
\start
%
	\mbox{(\ref{eq:260604c})}
%
\just\equiv{ \ref{eq:shuntingR} }
|
	lcbr4(
		i1 atmost  Parse . inj10 . nil
	)(
		i2 . (const 1 >< id) atmost Parse . inj0 . p2
	)(
		i2 . ((2+) . (conv ((tnb (const 5) . crflx pre))) >< id) atmost Parse . inj110 . conc
	)(
		i2 . ((2+) . (conv ((tnb e         . crflx (not pre)))) >< id) atmost Parse . inj111 . conc
	) 
|
\just\implied{ (\ref{eq:260604d}) ;  assume some |post'| such that |tnb e : not pre -> post'| }
|
	lcbr4(
		i1 atmost  Parse . inj10 . nil
	)(
		i2 . (const 1 >< id) atmost Parse . inj0 . p2
	)(
		i2 . ((2+) . fromBinary >< id) . (crflx post >< id) . conv conc atmost Parse . inj110
	)(
		i2 . ((2+) . fromBinary >< id) . (crflx post' >< id) . conv conc atmost Parse . inj111
	) 
|
\just\implied{ raise lower side by (\ref{eq:260604b}) + introduce |f| (see below) }
|
	lcbr4(
		i1 atmost  Parse . inj10 . nil
	)(
		i2 . (const 1 >< id) atmost Parse . inj0 . p2
	)(
		i2 . ((2+) . fromBinary >< id) . (nspan 5) atmost Parse . inj110
	)(
		i2 . ((2+) . fromBinary >< id) . f atmost Parse . inj111
	) 
|
\end{eqnarray*}
Since only functions are involved just above, it makes sense to further strengthen
|Parse| to a function |parse|, making it a deterministic parser:
\begin{eqnarray*}
\start
|
	lcbr4(
		parse . inj10 . nil = i1
	)(
		parse . inj0 . p2 = i2 . (const 1 >< id)
	)(
		parse . inj110 . nspan 5 = i2 . ((2+) . fromBinary >< id)
	)(
		parse . inj111 . f = i2 . ((2+) . fromBinary >< id)
	) 
|
\just\equiv{ \ref{eq:exteq}; definitions of |inj10| and |inj0|; \ref{eq:defx} ; \ref{eq:defsplit} }
|
	lcbr4(
		parse [1,0] = i1()
	)(
		parse(0 : r) = i2(1,r)
	)(
		parse(inj110 r) = i2(fromBinary a + 2, r') where (a,r') = nspan 5 r
	)(
		parse(inj111 r) = i2(fromBinary a + 2, y) where (a,y) = f r
	) 
|
\end{eqnarray*}
What remains to find is |post'| and |f| such that
\begin{eqnarray*}
\start |tnb e : not (ceil (pw 5)) -> post'|
\more  |f. conc . (crflx (post') >< id) atmost id|
\end{eqnarray*}

Here resides one of the trickiest parts of the whole |RLE| encoding, to be found in the
'E' function (\ref{eq:count}). Looking at the definition, we get
\[ |e a + 6 = 2*(minb a)| \]
where |minb a| is the minimum number of bits needed to encode |a|, which
always start with a |1|, for |a/=0|. Thus |tnb e a| has |minb a -6| leading
zeros. So, counting them and adding |6| gives us |minb a|.
In fact:
\begin{eqnarray*}
\start
|
	uncurry toNBits . split e id
|
\just={ uncurrying }
|
	toNBits (e a) a
|
\just={ definition of |toNBits| }
|
	toNBits (e a) a = nzeros ((e a) - length bits) ++ bits where bits = toBinary a 
|
\just={ |length (toBinary a) = minb a| } 
|
	toNBits (e a) a = nzeros ((e a) - minb a) ++ toBinary a 
|
\just={ definition of |e| }
|
	toNBits (e a) a = nzeros (2(minb a) -6 - minb a) ++ toBinary a 
|
\just={ definition (\ref{eq:tnb}) }
|
	tnb e = conc . split (nzeros .h) toBinary  where h a = minb a -6
|
\end{eqnarray*}
Thus:
\begin{eqnarray}
|
	tnb e . crflx(not pre) atmost conc . split (nzeros .h) toBinary  where h a = minb a -6
|
	\label{eq:260610a}
\end{eqnarray}

Then:
\begin{eqnarray*}
\start
|
	i2 . ((2+) . (conv ((tnb e  . crflx (not pre)))) >< id) atmost Parse . inj111 . conc
|
\just\implied{ (\ref{eq:260610a}) }
|
	i2 . ((2+) >< id) . (conv ((conc . split (nzeros .h) toBinary >< id)))  atmost Parse . inj111 . conc
|
\just\equiv{ \ref{eq:shuntingR} }
|
	i2 . ((2+) >< id) atmost Parse . inj111 . conc . (conc >< id) . (split (nzeros .h) toBinary  >< id)
|
\just\equiv{ associate to the right }
|
	i2 . ((2+) >< id) atmost Parse . inj111 .  conc . split (nzeros . h . p1) (conc . (toBinary >< id))
|
\end{eqnarray*}
It is clear from above that |nzeros . h . p1| is a form of encoding the length
of the bit string generated by |toBinary|, using zeros to represent such a number in binary. Lack of time prevents us from reaching
\begin{eqnarray*}
|
	i2 . ((2+) . fromBinary >< id) . uncurry nspan . ((6+) . length >< id) . cspan (==0) atmost Parse . inj111
|
\end{eqnarray*}
wherefrom 
\begin{eqnarray*}
	|f = uncurry nspan . ((6+) . length >< id) . cspan (==0)|
\end{eqnarray*}
can be calculated, finally leading to
\begin{spec}
parse [1,0] = Nothing
parse (0:r) = Just(1,r)
parse (1:(1:(0:r))) = Just(fromBinary a + 2, r')
    where (a,r') = nspan 5 r
parse (1:(1:(1:r))) = Just (fromBinary a + 2, r')
    where (a, r') = nspan (6 + length x) r'' ; (x, r'') = cspan (==0) r
parse _ = Nothing
\end{spec}
where |i1| and |i2| are transliterated to the |Maybe| data type, as required by Haskell's \emph{unfoldr} combinator used in (\ref{eq:uncounting}). Formally calculating this last step of the exercise is not immediate and is left for future work.

%	xxx Missing part:
%	
%	|takeWhile (/=1) . minb = nil| for positive inputs.
%	
%	TBC

\end{document}
