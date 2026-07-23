;;;; cffi-dotcl.lisp — CFFI-SYS backend for DotCL (Common Lisp on .NET).
;;;; Uses dotnet:alloc-mem/free-mem, dotnet:mem-read/write, dotnet:%ffi-call-ptr.

(in-package #:cffi-sys)

;;; flat-namespace: all symbols from all loaded libraries share one address space.
(pushnew 'flat-namespace *features*)

;;; Runtime OS probe.  dotcl fasls are OS-independent (one IL fasl is reused
;;; across environments differing in OS/CPU), so every OS decision here is made
;;; at LOAD time by querying the running CLR -- never with read-time #+/#- --
;;; exactly like trivial-features' tf-dotcl backend.
(defun %dotcl-windows-p ()
  "True when the running CLR is on Windows, via
RuntimeInformation.IsOSPlatform(OSPlatform.Windows)."
  (dotnet:static "System.Runtime.InteropServices.RuntimeInformation"
                 "IsOSPlatform"
                 (dotnet:static "System.Runtime.InteropServices.OSPlatform"
                                "get_Windows")))

;;; cffi-features consults :windows in *features*.  Push it only when actually
;;; on Windows, and independently of whether trivial-features has loaded yet.
;;; (On non-Windows, trivial-features / dotcl push the correct :unix keyword.)
(when (%dotcl-windows-p)
  (pushnew :windows *features*))

;;;# Symbol Case

(defun canonicalize-symbol-name-case (name)
  (declare (type string name))
  (string-upcase name))

;;;# Pointer representation
;;; In DotCL, a foreign pointer is a Fixnum (integer) representing the address.

(deftype foreign-pointer () 'integer)

(defun pointerp (ptr)
  (integerp ptr))

(defun pointer-eq (ptr1 ptr2)
  (= ptr1 ptr2))

(defun null-pointer ()
  0)

(defun null-pointer-p (ptr)
  (zerop ptr))

(defun inc-pointer (ptr offset)
  (+ ptr offset))

(defun make-pointer (address)
  address)

(defun pointer-address (ptr)
  ptr)

;;;# Memory allocation

(defun %foreign-alloc (size)
  "Allocate SIZE bytes on the heap and return a pointer (integer)."
  (dotnet:alloc-mem size))

(defun foreign-free (ptr)
  "Free a pointer allocated by %foreign-alloc."
  (dotnet:free-mem ptr))

(defmacro with-foreign-pointer ((var size &optional size-var) &body body)
  "Bind VAR to SIZE bytes of foreign memory. Always heap-allocated."
  (unless size-var (setf size-var (gensym "SIZE")))
  `(let* ((,size-var ,size)
          (,var (%foreign-alloc ,size-var)))
     (unwind-protect
          (progn ,@body)
       (foreign-free ,var))))

;;;# Shareable byte vectors

(defun make-shareable-byte-vector (size)
  (make-array size :element-type '(unsigned-byte 8)))

(defmacro with-pointer-to-vector-data ((ptr-var vector) &body body)
  "Bind PTR-VAR to a pointer to VECTOR's data (copy-in/copy-out)."
  (let ((vec (gensym "VEC")) (n (gensym "N")) (mem (gensym "MEM")))
    `(let* ((,vec ,vector)
            (,n (length ,vec))
            (,mem (dotnet:alloc-mem ,n)))
       (unwind-protect
            (progn
              (dotimes (i ,n)
                (dotnet:mem-write (aref ,vec i) :unsigned-char ,mem i))
              (let ((,ptr-var ,mem))
                ,@body)
              (dotimes (i ,n)
                (setf (aref ,vec i) (dotnet:mem-read :unsigned-char ,mem i))))
         (dotnet:free-mem ,mem)))))

;;;# Memory dereferencing

(defun %mem-ref (ptr type &optional (offset 0))
  (dotnet:mem-read type ptr offset))

(defun %mem-set (value ptr type &optional (offset 0))
  (dotnet:mem-write value type ptr offset)
  value)

;;;# Foreign type sizes and alignment

;;; cffi type → bytes (Windows x64)
(defun %foreign-type-size (type-keyword)
  (dotnet:type-size type-keyword))

(defun %foreign-type-alignment (type-keyword)
  (dotnet:type-align type-keyword))

;;;# Foreign function calling

;;; The size of C `long' is OS-dependent: 32-bit on Windows (LLP64), 64-bit on
;;; Unix (LP64).  Because a dotcl fasl is reused across OSes, this MUST be a
;;; load-time runtime decision, never read-time #+windows.  These specials are
;;; initialized from the OS probe every time the fasl loads, and the emitted
;;; call forms read them at call time (see %cffi->dotcl-type-form) so one fasl
;;; is correct on both Windows and Unix.
(defparameter *c-long-dotcl-type*          (if (%dotcl-windows-p) :int32 :int64))
(defparameter *c-unsigned-long-dotcl-type* (if (%dotcl-windows-p) :uint32 :uint64))

;;; Map cffi type keywords to dotcl FFI type keywords.  :long / :unsigned-long
;;; return the load-time-resolved value (also correct if called directly), but
;;; the funcall/callback paths route them through %cffi->dotcl-type-form so the
;;; decision is deferred to runtime rather than baked into the fasl.
(defun %cffi->dotcl-type (cffi-kw)
  (case cffi-kw
    (:char             :int8)
    (:unsigned-char    :uint8)
    (:short            :int16)
    (:unsigned-short   :uint16)
    (:int              :int32)
    (:unsigned-int     :uint32)
    (:long             *c-long-dotcl-type*)
    (:unsigned-long    *c-unsigned-long-dotcl-type*)
    (:long-long        :int64)
    (:unsigned-long-long :uint64)
    (:float            :float)
    (:double           :double)
    (:pointer          :ptr)
    (:bool             :bool)
    (:boolean          :bool)
    (:void             :void)
    (t                 cffi-kw)))

(defun %long-type-p (cffi-kw)
  (or (eq cffi-kw :long) (eq cffi-kw :unsigned-long)))

(defun %cffi->dotcl-type-form (cffi-kw)
  "A FORM, spliced into an emitted call, that yields the dotcl FFI type keyword
for CFFI-KW.  Non-long types become a constant quoted keyword; :long /
:unsigned-long become a reference to the load-time special so the long size
follows the OS the fasl is *run* on, not the OS it was compiled on."
  (case cffi-kw
    (:long          '*c-long-dotcl-type*)
    (:unsigned-long '*c-unsigned-long-dotcl-type*)
    (t              `',(%cffi->dotcl-type cffi-kw))))

(defun %emit-dtypes (types)
  "A FORM yielding the dotcl type list for TYPES.  Stays a compile-time constant
when no :long/:unsigned-long is present (fast path, shared literal); otherwise
built at call time so the long size is resolved on the running OS."
  (if (some #'%long-type-p types)
      `(list ,@(mapcar #'%cffi->dotcl-type-form types))
      `',(mapcar #'%cffi->dotcl-type types)))

(defun %emit-dret (rettype)
  "A FORM yielding the dotcl return-type keyword, or NIL for :void."
  (cond ((eq rettype :void) nil)
        ((%long-type-p rettype) (%cffi->dotcl-type-form rettype))
        (t `',(%cffi->dotcl-type rettype))))

;;; Parse interleaved (type val type val ... rettype) into (types vals rettype).
(defun %parse-funcall-args (args)
  (let (types fargs (return-type :void))
    (loop while args
          do (let ((type (pop args)))
               (cond ((eq type '&optional) nil)  ; varargs marker, skip
                     ((not args) (setq return-type type))
                     (t (push type types)
                        (push (pop args) fargs)))))
    (values (nreverse types) (nreverse fargs) return-type)))

;;; Cache: function name -> address (integer). Avoids symbol lookup on every call.
(defvar *%ffi-fn-cache* (make-hash-table :test #'equal))

(defun %find-ffi-fn (name)
  (or (gethash name *%ffi-fn-cache*)
      (let ((ptr (dotnet:find-symbol-any name)))
        (when ptr (setf (gethash name *%ffi-fn-cache*) ptr))
        ptr)))

(defmacro %foreign-funcall (name args &key library convention)
  "Call a foreign function NAME with ARGS (interleaved type/value pairs + rettype)."
  (declare (ignore library convention))
  (multiple-value-bind (types fargs rettype)
      (%parse-funcall-args args)
    (let ((ptr-var (gensym "FN")))
      `(let ((,ptr-var (%find-ffi-fn ,name)))
         (unless ,ptr-var
           (error "dotcl/cffi: foreign function ~S not found in any loaded library" ,name))
         (dotnet:%ffi-call-ptr ,ptr-var ,(%emit-dtypes types) ,(%emit-dret rettype) ,@fargs)))))

(defmacro %foreign-funcall-pointer (ptr args &key convention)
  "Call a foreign function via a pointer."
  (declare (ignore convention))
  (multiple-value-bind (types fargs rettype)
      (%parse-funcall-args args)
    `(dotnet:%ffi-call-ptr ,ptr ,(%emit-dtypes types) ,(%emit-dret rettype) ,@fargs)))

(defmacro %foreign-funcall-varargs (name fixed-args varargs &rest keys &key convention library)
  (declare (ignore convention library))
  `(%foreign-funcall ,name ,(append fixed-args varargs) ,@keys))

(defmacro %foreign-funcall-pointer-varargs (ptr fixed-args varargs &rest keys &key convention)
  (declare (ignore convention))
  `(%foreign-funcall-pointer ,ptr ,(append fixed-args varargs) ,@keys))

;;;# Callbacks
;;;
;;; A Lisp function is exposed to C as a native function pointer via
;;; dotnet:make-ffi-callback. On x64/ARM64 there is a single calling convention,
;;; so :convention (cdecl/stdcall) is accepted but not distinguished.

(defvar *callbacks* (make-hash-table :test 'eq)
  "Map of callback name -> native function pointer (integer).")

(defmacro %defcallback (name rettype arg-names arg-types body &key convention)
  (declare (ignore convention))
  ;; BODY is a single form (CFFI's inverse-translate-objects wraps the user body
  ;; in a LET for argument translation), so splice it with , not ,@.
  `(setf (gethash ',name *callbacks*)
         (dotnet:make-ffi-callback
          (lambda (,@arg-names) ,body)
          (list ,@(mapcar #'%cffi->dotcl-type-form arg-types))
          ,(%cffi->dotcl-type-form rettype))))

(defun %callback (name)
  (or (gethash name *callbacks*)
      (error "dotcl/cffi: undefined callback: ~S" name)))

;;;# Loading and closing foreign libraries

;;; Returns an integer handle (IntPtr value) for the loaded library.
(defun %load-foreign-library (name path)
  (declare (ignore name))
  (let ((path-str (if (stringp path) path (namestring path))))
    (dotnet:load-library path-str)))

(defun %close-foreign-library (handle)
  (dotnet:free-library handle))

(defun native-namestring (pathname)
  (if (stringp pathname) pathname (namestring pathname)))

;;;# Foreign globals / symbol lookup

(defun %foreign-symbol-pointer (name library)
  (declare (ignore library))
  (dotnet:find-symbol-any name))

;;;# defcfun-helper-forms
;;;
;;; Intentionally NOT defined for the dotcl backend. CFFI core (functions.lisp)
;;; installs a default DEFCFUN-HELPER-FORMS that routes DEFCFUN through
;;; %FOREIGN-FUNCALL when the backend does not provide one — which is exactly
;;; what we want here (like the SBCL and CCL backends, which also omit it).
