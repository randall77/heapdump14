package read

import (
	"bufio"
	"debug/dwarf"
	"debug/elf"
	"debug/macho"
	"debug/pe"
	"encoding/binary"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strings"
)

type FieldKind int
type TypeKind int

const (
	FieldKindEol    FieldKind = 0
	FieldKindPtr              = 1
	FieldKindIface            = 2
	FieldKindEface            = 3
	FieldKindString           = 4
	FieldKindSlice            = 5

	FieldKindBool       FieldKind = 6
	FieldKindUInt8                = 7
	FieldKindSInt8                = 8
	FieldKindUInt16               = 9
	FieldKindSInt16               = 10
	FieldKindUInt32     FieldKind = 11
	FieldKindSInt32               = 12
	FieldKindUInt64     FieldKind = 13
	FieldKindSInt64               = 14
	FieldKindFloat32              = 15
	FieldKindFloat64              = 16
	FieldKindComplex64            = 17
	FieldKindComplex128           = 18

	FieldKindBytes4      = 19
	FieldKindBytes8      = 20
	FieldKindBytes16     = 21
	FieldKindBytesElided = 22

	TypeKindObject       TypeKind = 0
	TypeKindArray                 = 1
	TypeKindChan                  = 2
	TypeKindConservative          = 127

	tagEOF         = 0
	tagObject      = 1
	tagOtherRoot   = 2
	tagType        = 3
	tagGoRoutine   = 4
	tagStackFrame  = 5
	tagParams      = 6
	tagFinalizer   = 7
	tagItab        = 8
	tagOSThread    = 9
	tagMemStats    = 10
	tagQFinal      = 11
	tagData        = 12
	tagBss         = 13
	tagDefer       = 14
	tagPanic       = 15
	tagMemProf     = 16
	tagAllocSample = 17

	// DWARF constants
	dw_op_call_frame_cfa = 156
	dw_op_consts         = 17
	dw_op_plus           = 34
	dw_op_plus_uconst    = 35
	dw_op_addr           = 3
	dw_ate_boolean       = 2
	dw_ate_complex_float = 3 // complex64/complex128
	dw_ate_float         = 4 // float32/float64
	dw_ate_signed        = 5 // int8/int16/int32/int64/int
	dw_ate_unsigned      = 7 // uint8/uint16/uint32/uint64/uint/uintptr

	// Size of buckets for FindObj.  Bigger buckets use less memory
	// but make FindObj take longer.  512 byte buckets use about 1.5%
	// of the total heap size and require us to look at at most
	// 64 objects.
	bucketSize = 512
)

type Dump struct {
	Order        binary.ByteOrder
	PtrSize      uint64 // in bytes
	HeapStart    uint64
	HeapEnd      uint64
	TheChar      byte
	Experiment   string
	Ncpu         uint64
	Types        []*Type
	objects      []object
	Frames       []*StackFrame
	Goroutines   []*GoRoutine
	Otherroots   []*OtherRoot
	Finalizers   []*Finalizer  // pending finalizers, object still live
	QFinal       []*QFinalizer // finalizers which are ready to run
	Osthreads    []*OSThread
	Memstats     *runtime.MemStats
	Data         *Data
	Bss          *Data
	Defers       []*Defer
	Panics       []*Panic
	MemProf      []*MemProfEntry
	AllocSamples []*AllocSample

	// handle to dump file
	r io.ReaderAt

	buf []byte // temporary space for Contents calls

	edges []Edge // temporary space for Edges calls

	// list of full types, indexed by ID
	FTList []*FullType

	// map from type address to type
	TypeMap map[uint64]*Type

	// map from itab address to the type address that itab address represents.
	ItabMap map[uint64]uint64

	// Data structure for fast lookup of objects.  Divides the heap
	// into chunks of bucketSize bytes.  For each bucket, we keep
	// track of the lowest address object that has any of its
	// bytes in that bucket.
	bucketSize uint64
	idx        []ObjId
}

type Type struct {
	Name         string // not necessarily unique
	Size         uint64
	interfaceptr bool    // interfaces with this type have a pointer in their data field
	Fields       []Field // ordered in increasing offset order

	Addr uint64
}

type FullType struct {
	Id     int
	Size   uint64
	GCSig  string
	Name   string
	Fields []Field
	Type   dwarfType
}

// An edge is a directed connection between two objects.  The source
// object is implicit.  An edge includes information about where it
// leaves the source object and where it lands in the destination obj.
type Edge struct {
	To         ObjId  // index of target object in array
	FromOffset uint64 // offset in source object where ptr was found
	ToOffset   uint64 // offset in destination object where ptr lands

	// name of field in the source object, if known
	FieldName string
}

// object represents an object in the heap.
// There will be a lot of these.  They need to be small.
type object struct {
	Ft     *FullType
	offset int64 // position of object contents in dump file
	Addr   uint64
}

type ObjId int

const (
	ObjNil ObjId = -1
)

// NumObjects returns the number of objects in the heap.  Valid
// ObjIds for other calls are from 0 to NumObjects()-1.
func (d *Dump) NumObjects() int {
	return len(d.objects)
}
func (d *Dump) Contents(i ObjId) []byte {
	x := d.objects[i]
	b := d.buf
	if uint64(cap(b)) < x.Ft.Size {
		b = make([]byte, x.Ft.Size)
		d.buf = b
	}
	b = b[:x.Ft.Size]
	_, err := d.r.ReadAt(b, x.offset)
	if err != nil {
		// TODO: propagate to caller
		log.Fatal(err)
	}
	return b
}
func (d *Dump) Addr(x ObjId) uint64 {
	return d.objects[x].Addr
}
func (d *Dump) Size(x ObjId) uint64 {
	return d.objects[x].Ft.Size
}
func (d *Dump) Ft(x ObjId) *FullType {
	return d.objects[x].Ft
}

// FindObj returns the object id containing the address addr, or -1 if no object contains addr.
func (d *Dump) FindObj(addr uint64) ObjId {
	if addr < d.HeapStart || addr >= d.HeapEnd { // quick exit.  Includes nil.
		return ObjNil
	}
	// linear search among all the objects that map to the same bucketSize-byte bucket.
	for i := d.idx[(addr-d.HeapStart)/bucketSize]; i < ObjId(len(d.objects)); i++ {
		x := &d.objects[i]
		if addr < x.Addr {
			return ObjNil
		}
		if addr < x.Addr+x.Ft.Size {
			return ObjId(i)
		}
	}
	return ObjNil
}

func (d *Dump) Edges(i ObjId) []Edge {
	x := &d.objects[i]
	e := d.edges[:0]
	b := d.Contents(i)
	for _, f := range x.Ft.Fields {
		//fmt.Printf("field %d %s %d\n", f.Kind, f.Name, f.Offset)
		switch f.Kind {
		case FieldKindPtr:
			p := readPtr(d, b[f.Offset:])
			y := d.FindObj(p)
			if y != ObjNil {
				e = append(e, Edge{y, f.Offset, p - d.objects[y].Addr, f.Name})
			}
		case FieldKindEface:
			taddr := readPtr(d, b[f.Offset:])
			if taddr != 0 {
				t := d.TypeMap[taddr]
				if t == nil {
					log.Fatalf("Edges: can't find eface type %x", taddr)
				}
				if t.interfaceptr {
					p := readPtr(d, b[f.Offset+d.PtrSize:])
					y := d.FindObj(p)
					if y != ObjNil {
						e = append(e, Edge{y, f.Offset + d.PtrSize, p - d.objects[y].Addr, f.Name})
					}
				}
			}
		case FieldKindIface:
			itabaddr := readPtr(d, b[f.Offset:])
			if itabaddr != 0 {
				taddr := d.ItabMap[itabaddr]
				if taddr == 0 {
					log.Fatalf("Edges: can't find itab %x", itabaddr)
				}
				t := d.TypeMap[taddr]
				if t == nil {
					log.Fatalf("Edges: can't find iface type %x", taddr)
				}
				if t.interfaceptr {
					p := readPtr(d, b[f.Offset+d.PtrSize:])
					y := d.FindObj(p)
					if y != ObjNil {
						e = append(e, Edge{y, f.Offset + d.PtrSize, p - d.objects[y].Addr, f.Name})
					}
				}
			}
		default:
			continue
		}
	}
	d.edges = e
	return e
}

type OtherRoot struct {
	Description string
	Edges       []Edge

	toaddr uint64
}

// Object obj has a finalizer.
type Finalizer struct {
	obj  uint64
	fn   uint64 // function to be run (a FuncVal*)
	code uint64 // code ptr (fn->fn)
	fint uint64 // type of function argument
	ot   uint64 // type of object
}

// Finalizer that's ready to run
type QFinalizer struct {
	obj   uint64
	fn    uint64 // function to be run (a FuncVal*)
	code  uint64 // code ptr (fn->fn)
	fint  uint64 // type of function argument
	ot    uint64 // type of object
	Edges []Edge
}

type Defer struct {
	addr uint64
	gp   uint64
	argp uint64
	pc   uint64
	fn   uint64
	code uint64
	link uint64
}

type Panic struct {
	addr uint64
	gp   uint64
	typ  uint64
	data uint64
	defr uint64
	link uint64
}

type MemProfFrame struct {
	Func string
	File string
	Line uint64
}

type MemProfEntry struct {
	addr   uint64
	size   uint64
	stack  []MemProfFrame
	allocs uint64
	frees  uint64
}

type AllocSample struct {
	Addr uint64        // address of object
	Prof *MemProfEntry // record of allocation site
}

type Data struct {
	Addr   uint64
	Data   []byte
	Fields []Field
	Edges  []Edge
}

type OSThread struct {
	addr   uint64
	id     uint64
	procid uint64
}

// A Field is a location in an object where there
// might be a pointer.
type Field struct {
	Kind     FieldKind
	Offset   uint64
	Name     string
	BaseType string // base type for Ptr, Slice, Iface ("" if not known)
}

type GoRoutine struct {
	Bos  *StackFrame // frame at the top of the stack (i.e. currently running)
	Ctxt ObjId

	Addr         uint64
	bosaddr      uint64
	Goid         uint64
	Gopc         uint64
	Status       uint64
	IsSystem     bool
	IsBackground bool
	WaitSince    uint64
	WaitReason   string
	ctxtaddr     uint64
	maddr        uint64
	deferaddr    uint64
	panicaddr    uint64
}

type StackFrame struct {
	Name      string
	Parent    *StackFrame
	Goroutine *GoRoutine
	Depth     uint64
	Data      []byte
	Edges     []Edge

	Addr      uint64
	childaddr uint64
	entry     uint64
	pc        uint64
	Fields    []Field
}

// both an io.Reader and an io.ByteReader
type Reader interface {
	Read(p []byte) (n int, err error)
	ReadByte() (c byte, err error)
}

func readUint64(r Reader) uint64 {
	x, err := binary.ReadUvarint(r)
	if err != nil {
		log.Fatal(err)
	}
	return x
}

func readNBytes(r Reader, n uint64) []byte {
	s := make([]byte, n)
	_, err := io.ReadFull(r, s)
	if err != nil {
		log.Fatal(err)
	}
	return s
}

func readBytes(r Reader) []byte {
	n := readUint64(r)
	return readNBytes(r, n)
}

func readString(r Reader) string {
	return string(readBytes(r))
}

func readBool(r Reader) bool {
	b, err := r.ReadByte()
	if err != nil {
		log.Fatal(err)
	}
	return b != 0
}

func readFields(r Reader) []Field {
	var x []Field
	for {
		kind := FieldKind(readUint64(r))
		if kind == FieldKindEol {
			// TODO: sort by offset, or check that it is sorted
			return x
		}
		x = append(x, Field{Kind: kind, Offset: readUint64(r)})
	}
}

// A Reader that can tell you its current offset in the file.
type myReader struct {
	r   *bufio.Reader
	cnt int64
}

func (r *myReader) Read(p []byte) (n int, err error) {
	n, err = r.r.Read(p)
	r.cnt += int64(n)
	return
}
func (r *myReader) ReadByte() (c byte, err error) {
	c, err = r.r.ReadByte()
	if err != nil {
		return
	}
	r.cnt++
	return
}
func (r *myReader) ReadLine() (line []byte, isPrefix bool, err error) {
	line, isPrefix, err = r.r.ReadLine()
	r.cnt += int64(len(line)) + 1
	return
}
func (r *myReader) Skip(n int64) error {
	k, err := io.CopyN(ioutil.Discard, r.r, n)
	r.cnt += k
	return err
}
func (r *myReader) Count() int64 {
	return r.cnt
}

type tkey struct {
	size  uint64
	gcsig string
}

func (d *Dump) makeFullType(size uint64, gcmap string) *FullType {
	name := fmt.Sprintf("%d_%s", size, gcmap)
	ft := &FullType{len(d.FTList), size, gcmap, name, nil, nil}
	d.FTList = append(d.FTList, ft)
	return ft
}

// Reads heap dump into memory.
func rawRead(filename string) *Dump {
	file, err := os.Open(filename)
	if err != nil {
		log.Fatal(err)
	}
	r := &myReader{r: bufio.NewReader(file)}

	// check for header
	hdr, prefix, err := r.ReadLine()
	if err != nil {
		log.Fatal(err)
	}
	if prefix || string(hdr) != "go1.4 heap dump" {
		log.Fatal("not a go1.4 heap dump file")
	}

	var d Dump
	d.r = file
	d.ItabMap = map[uint64]uint64{}
	d.TypeMap = map[uint64]*Type{}
	ftmap := map[tkey]*FullType{} // full type dedup
	memprof := map[uint64]*MemProfEntry{}
	var sig []byte // buffer for reading a garbage collection signature
	for {
		kind := readUint64(r)
		switch kind {
		case tagObject:
			obj := object{}
			obj.Addr = readUint64(r)
			size := readUint64(r)
			obj.offset = r.Count()
			r.Skip(int64(size))

			// build a "signature" for the object.  This is its type
			// as far as the garbage collector is concerned.
			sig = sig[:0]
			var offset uint64
		gcloop:
			for {
				// P = pointer
				// S = scalar
				// I = iface
				// E = eface
				switch FieldKind(readUint64(r)) {
				case FieldKindPtr:
					for off := readUint64(r); offset < off; offset += d.PtrSize {
						sig = append(sig, 'S')
					}
					sig = append(sig, 'P')
					offset += d.PtrSize
				case FieldKindIface:
					for off := readUint64(r); offset < off; offset += d.PtrSize {
						sig = append(sig, 'S')
					}
					sig = append(sig, 'I', 'I')
					offset += 2 * d.PtrSize
				case FieldKindEface:
					for off := readUint64(r); offset < off; offset += d.PtrSize {
						sig = append(sig, 'S')
					}
					sig = append(sig, 'E', 'E')
					offset += 2 * d.PtrSize
				case FieldKindEol:
					break gcloop
				}
			}
			gcsig := string(sig)
			k := tkey{size, gcsig}
			ft := ftmap[k]
			if ft == nil {
				ft = d.makeFullType(size, gcsig)
				ftmap[k] = ft
			}
			obj.Ft = ft
			d.objects = append(d.objects, obj)
		case tagEOF:
			return &d
		case tagOtherRoot:
			t := &OtherRoot{}
			t.Description = readString(r)
			t.toaddr = readUint64(r)
			d.Otherroots = append(d.Otherroots, t)
		case tagType:
			typ := &Type{}
			typ.Addr = readUint64(r)
			typ.Size = readUint64(r)
			typ.Name = readString(r)
			typ.interfaceptr = readBool(r)
			// Note: there may be duplicate type records in a dump.
			// The duplicates get thrown away here.
			if _, ok := d.TypeMap[typ.Addr]; !ok {
				d.TypeMap[typ.Addr] = typ
				d.Types = append(d.Types, typ)
			}
			//fmt.Printf("type %x\n", typ.Addr)
		case tagGoRoutine:
			g := &GoRoutine{}
			g.Addr = readUint64(r)
			g.bosaddr = readUint64(r)
			g.Goid = readUint64(r)
			g.Gopc = readUint64(r)
			g.Status = readUint64(r)
			g.IsSystem = readBool(r)
			g.IsBackground = readBool(r)
			g.WaitSince = readUint64(r)
			g.WaitReason = readString(r)
			g.ctxtaddr = readUint64(r)
			g.maddr = readUint64(r)
			g.deferaddr = readUint64(r)
			g.panicaddr = readUint64(r)
			d.Goroutines = append(d.Goroutines, g)
		case tagStackFrame:
			t := &StackFrame{}
			t.Addr = readUint64(r)
			t.Depth = readUint64(r)
			t.childaddr = readUint64(r)
			t.Data = readBytes(r)
			t.entry = readUint64(r)
			t.pc = readUint64(r)
			readUint64(r) // continpc
			t.Name = readString(r)
			t.Fields = readFields(r)
			d.Frames = append(d.Frames, t)
		case tagParams:
			if readUint64(r) == 0 {
				d.Order = binary.LittleEndian
			} else {
				d.Order = binary.BigEndian
			}
			d.PtrSize = readUint64(r)
			d.HeapStart = readUint64(r)
			d.HeapEnd = readUint64(r)
			d.TheChar = byte(readUint64(r))
			d.Experiment = readString(r)
			d.Ncpu = readUint64(r)
		case tagFinalizer:
			t := &Finalizer{}
			t.obj = readUint64(r)
			t.fn = readUint64(r)
			t.code = readUint64(r)
			t.fint = readUint64(r)
			t.ot = readUint64(r)
			d.Finalizers = append(d.Finalizers, t)
		case tagQFinal:
			t := &QFinalizer{}
			t.obj = readUint64(r)
			t.fn = readUint64(r)
			t.code = readUint64(r)
			t.fint = readUint64(r)
			t.ot = readUint64(r)
			d.QFinal = append(d.QFinal, t)
		case tagData:
			t := &Data{}
			t.Addr = readUint64(r)
			t.Data = readBytes(r)
			t.Fields = readFields(r)
			d.Data = t
		case tagBss:
			t := &Data{}
			t.Addr = readUint64(r)
			t.Data = readBytes(r)
			t.Fields = readFields(r)
			d.Bss = t
		case tagItab:
			addr := readUint64(r)
			typaddr := readUint64(r)
			d.ItabMap[addr] = typaddr
		case tagOSThread:
			t := &OSThread{}
			t.addr = readUint64(r)
			t.id = readUint64(r)
			t.procid = readUint64(r)
			d.Osthreads = append(d.Osthreads, t)
		case tagMemStats:
			t := &runtime.MemStats{}
			t.Alloc = readUint64(r)
			t.TotalAlloc = readUint64(r)
			t.Sys = readUint64(r)
			t.Lookups = readUint64(r)
			t.Mallocs = readUint64(r)
			t.Frees = readUint64(r)
			t.HeapAlloc = readUint64(r)
			t.HeapSys = readUint64(r)
			t.HeapIdle = readUint64(r)
			t.HeapInuse = readUint64(r)
			t.HeapReleased = readUint64(r)
			t.HeapObjects = readUint64(r)
			t.StackInuse = readUint64(r)
			t.StackSys = readUint64(r)
			t.MSpanInuse = readUint64(r)
			t.MSpanSys = readUint64(r)
			t.MCacheInuse = readUint64(r)
			t.MCacheSys = readUint64(r)
			t.BuckHashSys = readUint64(r)
			t.GCSys = readUint64(r)
			t.OtherSys = readUint64(r)
			t.NextGC = readUint64(r)
			t.LastGC = readUint64(r)
			t.PauseTotalNs = readUint64(r)
			for i := 0; i < 256; i++ {
				t.PauseNs[i] = readUint64(r)
			}
			t.NumGC = uint32(readUint64(r))
			d.Memstats = t
		case tagDefer:
			t := &Defer{}
			t.addr = readUint64(r)
			t.gp = readUint64(r)
			t.argp = readUint64(r)
			t.pc = readUint64(r)
			t.fn = readUint64(r)
			t.code = readUint64(r)
			t.link = readUint64(r)
			d.Defers = append(d.Defers, t)
		case tagPanic:
			t := &Panic{}
			t.addr = readUint64(r)
			t.gp = readUint64(r)
			t.typ = readUint64(r)
			t.data = readUint64(r)
			t.defr = readUint64(r)
			t.link = readUint64(r)
			d.Panics = append(d.Panics, t)
		case tagMemProf:
			t := &MemProfEntry{}
			key := readUint64(r)
			t.size = readUint64(r)
			nstk := readUint64(r)
			for i := uint64(0); i < nstk; i++ {
				fn := readString(r)
				file := readString(r)
				line := readUint64(r)
				// TODO: intern fn, file.  They will repeat a lot.
				t.stack = append(t.stack, MemProfFrame{fn, file, line})
			}
			t.allocs = readUint64(r)
			t.frees = readUint64(r)
			d.MemProf = append(d.MemProf, t)
			memprof[key] = t
		case tagAllocSample:
			t := &AllocSample{}
			t.Addr = readUint64(r)
			t.Prof = memprof[readUint64(r)]
			d.AllocSamples = append(d.AllocSamples, t)
		default:
			log.Fatal("unknown record kind ", kind)
		}
	}
	// TODO: any easy way to truncate the objects array?  We could
	// reclaim the fraction that append() added but we didn't need.
}

func getDwarf(execname string) *dwarf.Data {
	e, err := elf.Open(execname)
	if err == nil {
		defer e.Close()
		d, err := e.DWARF()
		if err == nil {
			return d
		}
	}
	m, err := macho.Open(execname)
	if err == nil {
		defer m.Close()
		d, err := m.DWARF()
		if err == nil {
			return d
		}
	}
	p, err := pe.Open(execname)
	if err == nil {
		defer p.Close()
		d, err := p.DWARF()
		if err == nil {
			return d
		}
	}
	log.Fatal("can't get dwarf info from executable", err)
	return nil
}

func readUleb(b []byte) ([]byte, uint64) {
	r := uint64(0)
	s := uint(0)
	for {
		x := b[0]
		b = b[1:]
		r |= uint64(x&127) << s
		if x&128 == 0 {
			break
		}
		s += 7

	}
	return b, r
}
func readSleb(b []byte) ([]byte, int64) {
	c, v := readUleb(b)
	// sign extend
	k := (len(b) - len(c)) * 7
	return c, int64(v) << uint(64-k) >> uint(64-k)
}

func joinNames(a, b string) string {
	if a == "" {
		return b
	}
	if b == "" {
		return a
	}
	return fmt.Sprintf("%s.%s", a, b)
}

type dwarfType interface {
	// Name returns the name of this type
	Name() string
	// Size returns the size of this type in bytes
	Size() uint64
	// Fields returns a list of fields within the object, in increasing offset order.
	Fields() []Field
	// dwarfFields returns a list of fields within the type.
	// The list is "flattened", so only base & ptr types remain. (TODO: and func, for now)
	// We call this dynamically instead of building it for each type
	// when the type is constructed, so we avoid constructing this list for
	// crazy types that are never instantiated, e.g. [1000000000]byte.
	dwarfFields() []dwarfTypeMember
}
type dwarfTypeImpl struct {
	name    string
	size    uint64
	fields  []Field
	dFields []dwarfTypeMember
}
type dwarfBaseType struct {
	dwarfTypeImpl
	encoding int64
}
type dwarfTypedef struct {
	dwarfTypeImpl
	type_ dwarfType
}
type dwarfStructType struct {
	dwarfTypeImpl
	members []dwarfTypeMember
	isSlice bool
}
type dwarfTypeMember struct {
	offset uint64
	name   string
	type_  dwarfType
}
type dwarfPtrType struct {
	dwarfTypeImpl
	elem dwarfType
}
type dwarfArrayType struct {
	dwarfTypeImpl
	elem dwarfType
}
type dwarfFuncType struct {
	dwarfTypeImpl
}
type dwarfIfaceType struct {
	dwarfTypeImpl
}
type dwarfEfaceType struct {
	dwarfTypeImpl
}

func (t *dwarfTypeImpl) Name() string {
	return t.name
}
func (t *dwarfTypeImpl) Size() uint64 {
	return t.size
}
func (t *dwarfBaseType) Fields() []Field {
	if t.fields != nil {
		return t.fields
	}
	switch {
	case t.encoding == dw_ate_boolean:
		t.fields = append(t.fields, Field{FieldKindBool, 0, "", ""})
	case t.encoding == dw_ate_signed && t.size == 1:
		t.fields = append(t.fields, Field{FieldKindSInt8, 0, "", ""})
	case t.encoding == dw_ate_unsigned && t.size == 1:
		t.fields = append(t.fields, Field{FieldKindUInt8, 0, "", ""})
	case t.encoding == dw_ate_signed && t.size == 2:
		t.fields = append(t.fields, Field{FieldKindSInt16, 0, "", ""})
	case t.encoding == dw_ate_unsigned && t.size == 2:
		t.fields = append(t.fields, Field{FieldKindUInt16, 0, "", ""})
	case t.encoding == dw_ate_signed && t.size == 4:
		t.fields = append(t.fields, Field{FieldKindSInt32, 0, "", ""})
	case t.encoding == dw_ate_unsigned && t.size == 4:
		t.fields = append(t.fields, Field{FieldKindUInt32, 0, "", ""})
	case t.encoding == dw_ate_signed && t.size == 8:
		t.fields = append(t.fields, Field{FieldKindSInt64, 0, "", ""})
	case t.encoding == dw_ate_unsigned && t.size == 8:
		t.fields = append(t.fields, Field{FieldKindUInt64, 0, "", ""})
	case t.encoding == dw_ate_float && t.size == 4:
		t.fields = append(t.fields, Field{FieldKindFloat32, 0, "", ""})
	case t.encoding == dw_ate_float && t.size == 8:
		t.fields = append(t.fields, Field{FieldKindFloat64, 0, "", ""})
	case t.encoding == dw_ate_complex_float && t.size == 8:
		t.fields = append(t.fields, Field{FieldKindComplex64, 0, "", ""})
	case t.encoding == dw_ate_complex_float && t.size == 16:
		t.fields = append(t.fields, Field{FieldKindComplex128, 0, "", ""})
	default:
		log.Fatalf("unknown encoding type encoding=%d size=%d", t.encoding, t.size)
	}
	return t.fields
}
func (t *dwarfBaseType) dwarfFields() []dwarfTypeMember {
	if t.dFields != nil {
		return t.dFields
	}
	t.dFields = append(t.dFields, dwarfTypeMember{0, "", t}) // TODO: infinite recursion?
	return t.dFields
}

func (t *dwarfTypedef) Fields() []Field {
	return t.type_.Fields()
}
func (t *dwarfTypedef) dwarfFields() []dwarfTypeMember {
	return t.type_.dwarfFields()
}
func (t *dwarfTypedef) Size() uint64 {
	return t.type_.Size()
}

var unkBase = "unkBase"

func (t *dwarfPtrType) Fields() []Field {
	if t.fields == nil {
		if t.Name()[0] == '*' {
			t.fields = append(t.fields, Field{FieldKindPtr, 0, "", t.Name()[1:]})
		} else {
			t.fields = append(t.fields, Field{FieldKindPtr, 0, "", unkBase})
		}
	}
	return t.fields
}
func (t *dwarfPtrType) dwarfFields() []dwarfTypeMember {
	if t.dFields == nil {
		t.dFields = append(t.dFields, dwarfTypeMember{0, "", t})
	}
	return t.dFields
}

// We treat a func as a *uintptr.  (It is actually a pointer to a closure, which is
// in turn a pointer to code.)
// TODO: how do we deduce types of closure parameters???  We could look at the code
// pointer and figure it out somehow.
// TODO: parameterize size by d.PtrSize.
var dwarfCodePtr dwarfType = &dwarfBaseType{dwarfTypeImpl{"<codeptr>", 8, nil, nil}, dw_ate_unsigned}
var dwarfFunc dwarfType = &dwarfPtrType{dwarfTypeImpl{"*<closure>", 8, nil, nil}, dwarfCodePtr}

func (t *dwarfFuncType) Fields() []Field {
	if t.fields == nil {
		t.fields = append(t.fields, Field{FieldKindPtr, 0, "", unkBase})
	}
	return t.fields
}

func (t *dwarfFuncType) dwarfFields() []dwarfTypeMember {
	if t.dFields == nil {
		t.dFields = append(t.dFields, dwarfTypeMember{0, "", dwarfFunc})
	}
	return t.dFields
}

func (t *dwarfStructType) Fields() []Field {
	if t.fields != nil {
		return t.fields
	}
	// Iterate over members, flatten fields.
	// Don't look inside strings, interfaces, slices.
	switch {
	case t.name == "string":

		t.fields = append(t.fields, Field{FieldKindPtr, 0, "", ""}, Field{FieldKindUInt64, 0, "", ""}) // TODO: uint32 for 32-bit?
	case t.name == "runtime.iface":
		t.fields = append(t.fields, Field{FieldKindPtr, 0, "", unkBase}, Field{FieldKindPtr, 0, "", unkBase})
	case t.name == "runtime.eface":
		t.fields = append(t.fields, Field{FieldKindEface, 0, "", ""}, Field{FieldKindEface, 0, "", ""})
	default:
		for _, m := range t.members {
			for _, f := range m.type_.Fields() {
				t.fields = append(t.fields, Field{f.Kind, m.offset + f.Offset, joinNames(m.name, f.Name), f.BaseType})
			}
		}
	}
	return t.fields
}

func (t *dwarfStructType) dwarfFields() []dwarfTypeMember {
	if t.dFields != nil {
		return t.dFields
	}
	// Iterate over members, flatten fields.
	for _, m := range t.members {
		for _, f := range m.type_.dwarfFields() {
			t.dFields = append(t.dFields, dwarfTypeMember{m.offset + f.offset, joinNames(m.name, f.name), f.type_})
		}
	}
	return t.dFields
}

func (t *dwarfArrayType) Fields() []Field {
	if t.fields != nil {
		return t.fields
	}
	s := t.elem.Size()
	if s == 0 {
		return t.fields
	}
	n := t.Size() / s
	fields := t.elem.Fields()
	for i := uint64(0); i < n; i++ {
		for _, f := range fields {
			t.fields = append(t.fields, Field{f.Kind, i*s + f.Offset, joinNames(fmt.Sprintf("%d", i), f.Name), f.BaseType})
		}
	}
	return t.fields
}

func (t *dwarfArrayType) dwarfFields() []dwarfTypeMember {
	if t.dFields != nil {
		return t.dFields
	}
	s := t.elem.Size()
	if s == 0 {
		return t.dFields
	}
	n := t.Size() / s
	fields := t.elem.dwarfFields()
	for i := uint64(0); i < n; i++ {
		name := fmt.Sprintf("[%d]", i)
		for _, f := range fields {
			t.dFields = append(t.dFields, dwarfTypeMember{i*s + f.offset, joinNames(name, f.name), f.type_})
		}
	}
	return t.dFields
}

func (t *dwarfIfaceType) Fields() []Field {
	if t.fields == nil {
		t.fields = append(t.fields, Field{FieldKindIface, 0, "", ""})
	}
	return t.fields
}

func (t *dwarfIfaceType) dwarfFields() []dwarfTypeMember {
	if t.dFields == nil {
		t.dFields = append(t.dFields, dwarfTypeMember{0, "", t})
	}
	return t.dFields
}

func (t *dwarfEfaceType) Fields() []Field {
	if t.fields == nil {
		t.fields = append(t.fields, Field{FieldKindEface, 0, "", ""})
	}
	return t.fields
}

func (t *dwarfEfaceType) dwarfFields() []dwarfTypeMember {
	if t.dFields == nil {
		t.dFields = append(t.dFields, dwarfTypeMember{0, "", t})
	}
	return t.dFields
}

// baseType returns a string representing the base type of this dwarf type,
// or "" if the base type makes no sense.
func baseType(t dwarfType) string {
	switch t := t.(type) {
	case *dwarfPtrType:
		if t.elem == nil {
			return "&lt;unknown&gt;"
		} else {
			return t.elem.Name()
		}
		// TODO: iface, func?
	default:
		return ""
	}
}

// Some type names in the dwarf info don't match the corresponding
// type names in the binary.  We'll use the rewrites here to map
// between the two.
// TODO: just map names for now.  Do this conversion in the dwarf dumper?
type adjTypeName struct {
	matcher   *regexp.Regexp
	formatter string
}

var adjTypeNames = []adjTypeName{
	{regexp.MustCompile(`hash<(.*),(.*)>`), "map.hdr[%s]%s"},
	{regexp.MustCompile(`bucket<(.*),(.*)>`), "map.bucket[%s]%s"},
	// TODO: hchan<>?
}

// fix up dwarf names to match internal names
func fixName(s string) string {
	for _, a := range adjTypeNames {
		for {
			k := a.matcher.FindStringSubmatchIndex(s)
			if k == nil {
				break
			}
			var i []interface{}
			for j := 2; j < len(k); j += 2 {
				i = append(i, s[k[j]:k[j+1]])
			}
			s = s[:k[0]] + fmt.Sprintf(a.formatter, i...) + s[k[1]:]
		}
	}
	return s
}

// load a map of all of the dwarf types
func dwarfTypeMap(d *Dump, w *dwarf.Data) map[dwarf.Offset]dwarfType {
	t := make(map[dwarf.Offset]dwarfType)

	// pass 1: make a dwarfType for all of the types in the file
	r := w.Reader()
	for {
		e, err := r.Next()
		if err != nil {
			log.Fatal(err)
		}
		if e == nil {
			break
		}
		switch e.Tag {
		case dwarf.TagBaseType:
			x := new(dwarfBaseType)
			x.name = fixName(e.Val(dwarf.AttrName).(string))
			x.size = uint64(e.Val(dwarf.AttrByteSize).(int64))
			x.encoding = e.Val(dwarf.AttrEncoding).(int64)
			t[e.Offset] = x
		case dwarf.TagPointerType:
			x := new(dwarfPtrType)
			x.name = fixName(e.Val(dwarf.AttrName).(string))
			x.size = d.PtrSize
			t[e.Offset] = x
		case dwarf.TagStructType:
			name := fixName(e.Val(dwarf.AttrName).(string))
			if name == "runtime.iface" {
				x := new(dwarfIfaceType)
				x.name = name
				x.size = 2 * d.PtrSize
				t[e.Offset] = x
				continue
			}
			if name == "runtime.eface" {
				x := new(dwarfEfaceType)
				x.name = name
				x.size = 2 * d.PtrSize
				t[e.Offset] = x
				continue
			}
			x := new(dwarfStructType)
			x.name = name
			x.size = uint64(e.Val(dwarf.AttrByteSize).(int64))
			if len(x.name) >= 2 && x.name[:2] == "[]" {
				// TODO: check array/len/cap
				x.isSlice = true
			}
			t[e.Offset] = x
		case dwarf.TagArrayType:
			x := new(dwarfArrayType)
			x.name = fixName(e.Val(dwarf.AttrName).(string))
			x.size = uint64(e.Val(dwarf.AttrByteSize).(int64))
			t[e.Offset] = x
		case dwarf.TagTypedef:
			x := new(dwarfTypedef)
			x.name = fixName(e.Val(dwarf.AttrName).(string))
			t[e.Offset] = x
		case dwarf.TagSubroutineType:
			x := new(dwarfFuncType)
			x.name = fixName(e.Val(dwarf.AttrName).(string))
			x.size = d.PtrSize
			t[e.Offset] = x
		}
	}

	// pass 2: fill in / link up the types
	r = w.Reader()
	var currentStruct *dwarfStructType
	for {
		e, err := r.Next()
		if err != nil {
			log.Fatal(err)
		}
		if e == nil {
			break
		}
		switch e.Tag {
		case dwarf.TagTypedef:
			t[e.Offset].(*dwarfTypedef).type_ = t[e.Val(dwarf.AttrType).(dwarf.Offset)]
			if t[e.Offset].(*dwarfTypedef).type_ == nil {
				log.Fatalf("can't find referent for %s %d\n", t[e.Offset].(*dwarfTypedef).name, e.Val(dwarf.AttrType).(dwarf.Offset))
			}
		case dwarf.TagPointerType:
			i := e.Val(dwarf.AttrType)
			if i != nil {
				t[e.Offset].(*dwarfPtrType).elem = t[i.(dwarf.Offset)]
			} else {
				// The only nil cases are unsafe.Pointer and reflect.iword
				if t[e.Offset].Name() != "unsafe.Pointer" &&
					t[e.Offset].Name() != "crypto/x509._Ctype_CFTypeRef" {
					log.Fatalf("pointer without base pointer %s", t[e.Offset].Name())
				}
			}
		case dwarf.TagArrayType:
			t[e.Offset].(*dwarfArrayType).elem = t[e.Val(dwarf.AttrType).(dwarf.Offset)]
		case dwarf.TagStructType:
			name := e.Val(dwarf.AttrName).(string)
			switch name {
			case "runtime.iface":
				currentStruct = nil
			case "runtime.eface":
				currentStruct = nil
			default:
				currentStruct = t[e.Offset].(*dwarfStructType)
			}
		case dwarf.TagMember:
			if currentStruct == nil {
				continue
			}
			name := e.Val(dwarf.AttrName).(string)
			type_ := t[e.Val(dwarf.AttrType).(dwarf.Offset)]
			loc := e.Val(dwarf.AttrDataMemberLoc).([]uint8)
			var offset uint64
			if len(loc) == 0 {
				offset = 0
			} else if loc[0] == dw_op_plus_uconst {
				loc, offset = readUleb(loc[1:])
			} else if len(loc) >= 2 && loc[0] == dw_op_consts && loc[len(loc)-1] == dw_op_plus {
				loc, offset = readUleb(loc[1 : len(loc)-1])
				if len(loc) != 0 {
					break
				}
			} else {
				log.Fatalf("bad dwarf location spec %#v", loc)
			}
			currentStruct.members = append(currentStruct.members, dwarfTypeMember{offset, name, type_})
		}
	}
	return t
}

// globalRoots extracts a list of global variables.  The offsets are addresses.
func globalRoots(d *Dump, w *dwarf.Data, t map[dwarf.Offset]dwarfType) []dwarfTypeMember {
	var roots []dwarfTypeMember
	r := w.Reader()
	for {
		e, err := r.Next()
		if err != nil {
			log.Fatal(err)
		}
		if e == nil {
			break
		}
		if e.Tag != dwarf.TagVariable {
			continue
		}
		name := e.Val(dwarf.AttrName).(string)
		typ := t[e.Val(dwarf.AttrType).(dwarf.Offset)]
		locexpr := e.Val(dwarf.AttrLocation).([]uint8)
		if len(locexpr) == 0 || locexpr[0] != dw_op_addr {
			continue
		}
		loc := readPtr(d, locexpr[1:])
		if typ == nil {
			// lots of non-Go global symbols hit here (rodata, type..gc,
			// static function closures, ...)
			//fmt.Printf("nontyped global %s %d\n", name, loc)
			continue
		}
		roots = append(roots, dwarfTypeMember{loc, name, typ})
	}
	return roots
}

type frameLayout struct {
	// offset is distance down from FP
	locals []dwarfTypeMember
	// offset is distance up from first arg slot
	args []dwarfTypeMember
}

// frameLayouts returns a map from function names to frameLayouts describing that function's stack frame.
func frameLayouts(d *Dump, w *dwarf.Data, t map[dwarf.Offset]dwarfType) map[string]frameLayout {
	m := map[string]frameLayout{}
	var locals []dwarfTypeMember
	var args []dwarfTypeMember
	r := w.Reader()
	var funcname string
	for {
		e, err := r.Next()
		if err != nil {
			log.Fatal(err)
		}
		if e == nil {
			break
		}
		switch e.Tag {
		case dwarf.TagSubprogram:
			if funcname != "" {
				m[funcname] = frameLayout{locals, args}
				locals = nil
				args = nil
			}
			funcname = e.Val(dwarf.AttrName).(string)
		case dwarf.TagVariable:
			name := e.Val(dwarf.AttrName).(string)
			typ := t[e.Val(dwarf.AttrType).(dwarf.Offset)]
			loc := e.Val(dwarf.AttrLocation).([]uint8)
			if len(loc) == 0 || loc[0] != dw_op_call_frame_cfa {
				continue
			}
			var offset int64
			if len(loc) == 1 {
				offset = 0
			} else if len(loc) >= 3 && loc[1] == dw_op_consts && loc[len(loc)-1] == dw_op_plus {
				loc, offset = readSleb(loc[2 : len(loc)-1])
				if len(loc) != 0 {
					continue
				}
			}
			locals = append(locals, dwarfTypeMember{uint64(-offset), name, typ})
		case dwarf.TagFormalParameter:
			if e.Val(dwarf.AttrName) == nil {
				continue
			}
			name := e.Val(dwarf.AttrName).(string)
			typ := t[e.Val(dwarf.AttrType).(dwarf.Offset)]
			loc := e.Val(dwarf.AttrLocation).([]uint8)
			if len(loc) == 0 || loc[0] != dw_op_call_frame_cfa {
				continue
			}
			var offset int64
			if len(loc) == 1 {
				offset = 0
			} else if len(loc) >= 3 && loc[1] == dw_op_consts && loc[len(loc)-1] == dw_op_plus {
				loc, offset = readSleb(loc[2 : len(loc)-1])
				if len(loc) != 0 {
					continue
				}
			}
			args = append(args, dwarfTypeMember{uint64(offset), name, typ})
		}
	}
	if funcname != "" {
		m[funcname] = frameLayout{locals, args}
	}
	/* TODO: remove
	for name, layout := range m {
		log.Printf("func %s\n", name)
		for _, arg := range layout.args {
			log.Printf("    arg %s @ %d %s\n", arg.name, arg.offset, arg.type_.Name())
		}
		for _, local := range layout.locals {
			log.Printf("  local %s @ %d %s\n", local.name, local.offset, local.type_.Name())
		}
	}
	*/
	return m
}

// stack frames may be zero-sized, so we add call depth
// to the key to ensure uniqueness.
type frameKey struct {
	sp    uint64
	depth uint64
}

// appendEdge might add an edge to edges.  Returns new edges.
//   Requires data[off:] be a pointer
//   Adds an edge if that pointer points to a valid object.
func (d *Dump) appendEdge(edges []Edge, data []byte, off uint64, f Field) []Edge {
	p := readPtr(d, data[off:])
	q := d.FindObj(p)
	if q != ObjNil {
		edges = append(edges, Edge{q, off, p - d.objects[q].Addr, f.Name})
	}
	return edges
}

func (d *Dump) appendFields(edges []Edge, data []byte, fields []Field) []Edge {
	//fmt.Println("appending fields")
	for _, f := range fields {
		//fmt.Printf("field %d %d %s %s\n", f.Kind, f.Offset, f.Name, f.BaseType)
		off := f.Offset
		if off >= uint64(len(data)) {
			// TODO: what the heck is this?
			continue
		}
		switch f.Kind {
		case FieldKindPtr:
			edges = d.appendEdge(edges, data, off, f)
		case FieldKindString:
			edges = d.appendEdge(edges, data, off, f)
		case FieldKindSlice:
			edges = d.appendEdge(edges, data, off, f)
		case FieldKindEface:
			edges = d.appendEdge(edges, data, off, f)
			taddr := readPtr(d, data[off:])
			if taddr == 0 {
				continue // nil eface
			}
			t := d.TypeMap[taddr]
			if t == nil {
				log.Fatalf("can't find eface type %x", taddr)
			}
			if t.interfaceptr {
				edges = d.appendEdge(edges, data, off+d.PtrSize, f)
			}
		case FieldKindIface:
			itab := readPtr(d, data[off:])
			if itab == 0 {
				continue // nil iface
			}
			taddr, ok := d.ItabMap[itab]
			if !ok {
				log.Fatalf("can't find itab %x", itab)
			}
			if taddr == 0 {
				// this type has a non-pointer data field
				continue
			}
			t := d.TypeMap[taddr]
			if t == nil {
				log.Fatalf("can't find type for itab %x", taddr)
			}
			if t.interfaceptr {
				edges = d.appendEdge(edges, data, off+d.PtrSize, f)
			}
		}
	}
	return edges
}

// Matches a package path, e.g. code.google.com/p/go.tools/go/types.Var
var pathRegexp = regexp.MustCompile(`([\w./])+`)

// packageFromPath extracts the simple type name from the end of a package path.
// e.g. code.google.com/p/go.tools/go/types.Var -> types.Var
func typeFromPath(s string) string {
	i := strings.LastIndex(s, "/")
	if i == -1 {
		return s
	}
	return s[i+1:]
}

type propagateContext struct {
	d *Dump

	type2dwarf map[uint64]dwarfType
	itab2dwarf map[uint64]dwarfType

	// map from heap address to type at that address
	htypes map[uint64]dwarfType

	// queue of objects yet to be "scanned"
	addrq []uint64
}

func typePropagate(d *Dump, execname string) {
	fmt.Println("inferring types...")
	// TODO: special case the unsafe.Pointer in reflect.Value.  We can compute
	// the type of the thing it points to in this case.
	w := getDwarf(execname)
	t := dwarfTypeMap(d, w)

	var pc propagateContext
	pc.d = d

	// map from type name to dwarf type
	name2dwarf := map[string]dwarfType{}
	for _, typ := range t {
		name2dwarf[typ.Name()] = typ
	}

	// Some runtime type names have just package names instead of package paths, e.g.
	// gob.CommonType instead of encoding/gob.CommonType.  Figure out how the short
	// runtime names map to the long dwarf names.
	// TODO: matching types by name is very error prone.  There's got to be a better way.
	// For now, if there is a unique mapping from runtime type to dwarf type, use it.
	short2long := map[string][]dwarfType{}
	for n, dt := range name2dwarf {
		n = pathRegexp.ReplaceAllStringFunc(n, typeFromPath)
		short2long[n] = append(short2long[n], dt)
	}
	for n, a := range short2long {
		if len(a) == 1 {
			// the short name matches a unique long name.
			name2dwarf[n] = a[0]
			continue
		}
		log.Printf("Type %s is ambiguous.  Could be any of:", n)
		for _, dt := range a {
			log.Printf("  %s", dt.Name())
		}
		// TODO: use fields to disambiguate
	}

	// map from type address to dwarf type (for resolving efaces)
	pc.type2dwarf = map[uint64]dwarfType{}
	for _, typ := range d.TypeMap {
		dt := name2dwarf[typ.Name]
		if dt == nil {
			log.Printf("can't find type %s", typ.Name)
			continue
		}
		if typ.interfaceptr { // TODO: not right.  Fix.
			// We want typ to be the pointed-to object's type.
			// Interfaces store pointers directly, so the target's type
			// needs a dereference.
			dt = dt.dwarfFields()[0].type_.(*dwarfPtrType).elem
		}
		pc.type2dwarf[typ.Addr] = dt
	}

	// map from itab entry to dwarf type (for resolving ifaces)
	pc.itab2dwarf = map[uint64]dwarfType{}
	for itab, taddr := range d.ItabMap {
		dt, ok := pc.type2dwarf[taddr]
		pc.itab2dwarf[itab] = dt
		if !ok {
			log.Printf("can't find itab %x %x", itab, taddr)
		}
	}

	// map from heap address to type at that address
	pc.htypes = map[uint64]dwarfType{}

	// set types of objects which are pointed to by globals
	log.Printf("  Global variables...")
	for _, r := range globalRoots(d, w, t) {
		var data []byte
		switch {
		case r.offset >= d.Data.Addr && r.offset < d.Data.Addr+uint64(len(d.Data.Data)):
			data = d.Data.Data[r.offset-d.Data.Addr:]
		case r.offset >= d.Bss.Addr && r.offset < d.Bss.Addr+uint64(len(d.Bss.Data)):
			data = d.Bss.Data[r.offset-d.Bss.Addr:]
		default:
			// this happens for globals in, e.g., noptrbss
			//log.Printf("global address %s %x not in data [%x %x] or bss [%x %x]", r.name, r.offset, d.Data.Addr, d.Data.Addr+uint64(len(d.Data.Data)), d.Bss.Addr, d.Bss.Addr+uint64(len(d.Bss.Data)))
			continue
		}
		scanType(&pc, data[:r.type_.Size()], r.type_)
	}

	// set types of objects which are pointed to by stacks
	layouts := frameLayouts(d, w, t)
	log.Printf("  Stacks...")
	live := map[uint64]bool{}
	for _, g := range d.Goroutines {
		for r := g.Bos; r != nil; r = r.Parent {
			//log.Printf("func %s %x", r.Name, len(r.Data))
			for k := range live {
				delete(live, k)
			}
			for _, f := range r.Fields {
				switch f.Kind {
				case FieldKindPtr, FieldKindIface, FieldKindEface:
					//log.Printf("live %x\n", f.Offset)
					live[f.Offset] = true
				}
			}

			// find live pointers, propagate types along them
			for _, local := range layouts[r.Name].locals {
				i := uint64(len(r.Data)) - local.offset
				for j := uint64(0); j < local.type_.Size(); j += d.PtrSize {
					if live[i+j] {
						goto islive
					}
				}
				// local is dead, don't scan it
				// TODO: check to make sure all pointers are live or all pointers are
				// dead, not a mix of the two.
				continue
			islive:
				//log.Printf("  local %s/%s @ %x", r.Name, local.name, local.offset)
				scanType(&pc, r.Data[i:], local.type_)
			}

			for _, arg := range layouts[r.Name].args {
				//log.Printf("  arg %s/%s @ %x", r.Name, arg.name, arg.offset)
				scanType(&pc, r.Parent.Data[arg.offset:], arg.type_)
			}
		}
	}

	// propagate types
	for len(pc.addrq) > 0 {
		addr := pc.addrq[len(pc.addrq)-1]
		pc.addrq = pc.addrq[:len(pc.addrq)-1]
		typ := pc.htypes[addr]

		obj := d.FindObj(addr)
		if obj == ObjNil {
			// Can happen for pointers into stacks (from defers, say)
			//log.Printf("pointer %x is not to valid heap object addr=%s", addr, typ.Name())
			continue
		}
		base := d.Addr(obj)
		data := d.Contents(obj)[addr-base:]
		if typ.Size() > uint64(len(data)) {
			log.Fatalf("type=%s size=%d is too big for object %d", typ.Name(), typ.Size(), len(data))
		}
		data = data[:typ.Size()]
		scanType(&pc, data, typ)
	}

	// update types of known objects
	dwarfToFull := map[dwarfType]*FullType{}
	for i := 0; i < d.NumObjects(); i++ {
		x := ObjId(i)
		addr := d.Addr(x)
		if t, ok := pc.htypes[addr]; ok {
			ft, ok := dwarfToFull[t]
			if !ok {
				ft = &FullType{len(d.FTList), t.Size(), "", t.Name(), nil, t}
				d.FTList = append(d.FTList, ft)
				dwarfToFull[t] = ft
			}
			d.objects[x].Ft = ft
		}
	}
}

// "Scan" the object data as if it was the given type, possibly finding types
// of other objects that this one points to.
func scanType(pc *propagateContext, data []byte, typ dwarfType) {
	d := pc.d
	for _, f := range typ.dwarfFields() {
		if f.offset+f.type_.Size() > uint64(len(data)) {
			log.Fatalf("field past end of object %s %#v", typ.Name(), f)
		}
		switch t := f.type_.(type) {
		case *dwarfPtrType:
			if t.elem == nil {
				// t.elem is nil for unsafe.Pointer-like pointers
				continue
			}
			p := readPtr(d, data[f.offset:])
			setType(pc, p, t.elem)
		case *dwarfIfaceType:
			itab := readPtr(d, data[f.offset:])
			if itab == 0 {
				continue
			}
			it := pc.itab2dwarf[itab]
			if it == nil {
				log.Printf("can't find type in iface slot")
				log.Printf("  itab=%x", itab)
				log.Printf("  taddr=%x", d.ItabMap[itab])
				log.Printf("  typ=%s", d.TypeMap[d.ItabMap[itab]].Name)
				continue
			}
			p := readPtr(d, data[f.offset+d.PtrSize:])
			setType(pc, p, it)
		case *dwarfEfaceType:
			addr := readPtr(d, data[f.offset:])
			if addr == 0 {
				continue
			}
			it := pc.type2dwarf[addr]
			if it == nil {
				log.Printf("can't find type in eface slot")
				log.Printf("  addr=%x", addr)
				log.Printf("  typ=%s", d.TypeMap[addr].Name)
				continue
			}
			p := readPtr(d, data[f.offset+d.PtrSize:])
			setType(pc, p, it)
		case *dwarfBaseType:
			// nothing to do
		default:
			log.Fatalf("unknown type for field %#v", f)
		}
	}
}

func setType(pc *propagateContext, addr uint64, typ dwarfType) {
	d := pc.d
	if addr < d.HeapStart || addr >= d.HeapEnd {
		return
	}
	obj := d.FindObj(addr)
	if obj == ObjNil {
		// pointer into heap, but not to any object
		// can happen for defers pointing to stacks
		log.Printf("heap ptr %x doesn't point to an object", addr)
		return
	}
	if addr+typ.Size() > d.Addr(obj)+d.Size(obj) {
		log.Fatalf("dwarf type larger than object addr=%x typ=%s typsize=%x objaddr=%x objsize=%x", addr, typ.Name(), typ.Size(), d.Addr(obj), d.Size(obj))
	}
	
	checkType(d, addr, typ)

	if oldtyp, ok := pc.htypes[addr]; ok {
		if typ == oldtyp {
			return
		}
		// multiple types for the same address happen for channels of struct{},
		// the buf points back to the channel itself as type *byte.
		// TODO: make hchan.buf an unsafe.Pointer so we don't get this warning.
		log.Printf("type mismatch in heap %x %s %s", addr, oldtyp.Name(), typ.Name())

		// TODO: types with different names but identical layout are allowed.
		// TODO: different types are allowed, if one is a prefix of the other.  Check that.

		// Use the bigger type.
		if oldtyp.Size() >= typ.Size() {
			return
		}
	}

	// set type, queue object for scanning
	pc.htypes[addr] = typ
	pc.addrq = append(pc.addrq, addr)
	//fmt.Printf("%x: %s\n", addr, typ.Name())
}

// Check to make sure our type information is consistent.
// Dwarf info claims that the object at addr has type typ.  Check this info
// against the gcinfo types recorded in the dump.
func checkType(d *Dump, addr uint64, typ dwarfType) {
	// TODO: dwarf and runtime disagree about the layout of hchan<nonptrtype>
	if len(typ.Name()) >= 6 && typ.Name()[:6] == "hchan<" {
		return
	}

	obj := d.FindObj(addr)

	start := addr - d.Addr(obj)
	if start % d.PtrSize != 0 {
		// not aligned to a pointer - shouldn't contain any pointers
		for _, f := range typ.dwarfFields() {
			switch f.type_.(type) {
			case *dwarfPtrType:
				log.Fatalf("unaligned type %s has a pointer in it", typ.Name())
			case *dwarfIfaceType:
				log.Fatalf("unaligned type %s has an iface in it", typ.Name())
			case *dwarfEfaceType:
				log.Fatalf("unaligned type %s has an eface in it", typ.Name())
			}
		}
		return
	}
	s := d.Ft(obj).GCSig
	start /= d.PtrSize
	if start < uint64(len(s)) {
		s = s[start:]
	} else {
		s = ""
	}
	end := typ.Size() / d.PtrSize
	if end < uint64(len(s)) {
		s = s[:end]
	}
	// TODO: figure out how to check arrays.  Right now we only check one T at the target of any *T,
	// but for slices we should check lots of T (up to the capacity of the slice).
	n := 0
	for _, f := range typ.dwarfFields() {
		off := f.offset/d.PtrSize
		switch f.type_.(type) {
		case *dwarfPtrType:
			if off >= uint64(len(s)) || s[off] != 'P' {
				log.Fatalf("dwarf type %s has pointer @ %d, gc type %s does not", typ.Name(), off, s)
			}
			n++
		case *dwarfIfaceType:
			if off >= uint64(len(s)-1) || s[off] != 'I' && s[off+1] != 'I' {
				log.Fatalf("dwarf type %s has iface, gc type %s does not", typ.Name(), s)
			}
			n+=2
		case *dwarfEfaceType:
			if off >= uint64(len(s)-1) && s[off] != 'E' && s[off+1] != 'E' {
				log.Fatalf("dwarf type %s has eface, gc type %s does not", typ.Name(), s)
			}
			n+=2
		}
	}
	for _, c := range s {
		if c == 'P' || c == 'I' || c == 'E' {
			n--
		}
	}
	if n != 0 {
		log.Printf("dwarf type %s has a different number of pointers than gc type %s", typ.Name(), s)
	}
}

type nameType struct {
	name  string
	type_ dwarfType
}

// Names the fields it can for better debugging output
func nameWithDwarf(d *Dump, execname string) {
	w := getDwarf(execname)
	t := dwarfTypeMap(d, w)

	// name all frame fields
	layouts := frameLayouts(d, w, t)
	for _, g := range d.Goroutines {
		var c *StackFrame
		for r := g.Bos; r != nil; r = r.Parent {
			_, ok := layouts[r.Name]
			if !ok {
				log.Printf("no locals layout for %s", r.Name)
			}
			// make maps from offset to field name & type
			vars := map[uint64]nameType{}
			for _, local := range layouts[r.Name].locals {
				for _, f := range local.type_.dwarfFields() {
					vars[uint64(len(r.Data))-local.offset+f.offset] = nameType{joinNames(local.name, f.name), f.type_}
				}
			}
			if c != nil {
				_, ok := layouts[c.Name]
				if !ok {
					log.Printf("no locals layout for %s", c.Name)
				}
				for _, arg := range layouts[c.Name].args {
					for _, f := range arg.type_.dwarfFields() {
						vars[arg.offset+f.offset] = nameType{joinNames("outarg."+arg.name, f.name), f.type_}
					}
				}
			}

			for i, f := range r.Fields {
				v, ok := vars[f.Offset]
				if !ok {
					// Live ptr variable in frame has no dwarf type.  This seems to happen
					// for autotemps which get suppressed by the dwarf generator.
					//log.Printf("unknown field in %s @ %d (framesize=%d)", r.Name, f.Offset, len(r.Data))
					r.Fields[i].Name = fmt.Sprintf("~%d", f.Offset)
					r.Fields[i].BaseType = "&lt;unknown&gt;"
					continue
				}
				r.Fields[i].Name = v.name
				r.Fields[i].BaseType = baseType(v.type_)
			}
			c = r
		}
	}

	// name all globals
	gm := map[uint64]nameType{}
	for _, g := range globalRoots(d, w, t) {
		for _, f := range g.type_.dwarfFields() {
			gm[g.offset+f.offset] = nameType{joinNames(g.name, f.name), f.type_}
		}
	}
	for _, x := range []*Data{d.Data, d.Bss} {
		for i, f := range x.Fields {
			nt, ok := gm[x.Addr+f.Offset]
			if !ok {
				continue
			}
			x.Fields[i].Name = nt.name
			x.Fields[i].BaseType = baseType(nt.type_)
		}
	}
}

func link1(d *Dump) {
	// sort objects in increasing address order
	sort.Sort(byAddr(d.objects))

	// initialize index array
	d.idx = make([]ObjId, (d.HeapEnd-d.HeapStart+bucketSize-1)/bucketSize)
	for i := len(d.idx) - 1; i >= 0; i-- {
		d.idx[i] = ObjId(len(d.objects))
	}
	for i := len(d.objects) - 1; i >= 0; i-- {
		// Note: we iterate in reverse order so that the object with
		// the lowest address that intersects a bucket will win.
		lo := (d.objects[i].Addr - d.HeapStart) / bucketSize
		hi := (d.objects[i].Addr + d.objects[i].Ft.Size - 1 - d.HeapStart) / bucketSize
		for j := lo; j <= hi; j++ {
			d.idx[j] = ObjId(i)
		}
	}

	// initialize some maps used for linking
	frames := make(map[frameKey]*StackFrame, len(d.Frames))
	for _, x := range d.Frames {
		frames[frameKey{x.Addr, x.Depth}] = x
	}

	// link up frames in sequence
	for _, f := range d.Frames {
		if f.Depth == 0 {
			continue
		}
		g := frames[frameKey{f.childaddr, f.Depth - 1}]
		g.Parent = f
	}

	// link goroutines to frames & vice versa
	for _, g := range d.Goroutines {
		g.Bos = frames[frameKey{g.bosaddr, 0}]
		if g.Bos == nil {
			log.Fatal("bos missing")
		}
		for f := g.Bos; f != nil; f = f.Parent {
			f.Goroutine = g
		}
		x := d.FindObj(g.ctxtaddr)
		if x != ObjNil {
			g.Ctxt = x
		}
	}
}

func link2(d *Dump) {
	// link stack frames to objects
	for _, f := range d.Frames {
		f.Edges = d.appendFields(f.Edges, f.Data, f.Fields)
	}

	// link data roots
	for _, x := range []*Data{d.Data, d.Bss} {
		x.Edges = d.appendFields(x.Edges, x.Data, x.Fields)
	}

	// link other roots
	for _, r := range d.Otherroots {
		x := d.FindObj(r.toaddr)
		if x != ObjNil {
			r.Edges = append(r.Edges, Edge{x, 0, r.toaddr - d.objects[x].Addr, ""})
		}
	}

	// Add links for finalizers
	// TODO: how do we represent these?
	/*
		for _, f := range d.Finalizers {
			x := d.FindObj(f.obj)
			for _, addr := range []uint64{f.fn, f.fint, f.ot} {
				y := d.FindObj(addr)
				if x != nil && y != nil {
					x.Edges = append(x.Edges, Edge{y, 0, addr - y.Addr, "finalizer", 0})
				}
			}
		}
	*/
	for _, f := range d.QFinal {
		for _, addr := range []uint64{f.obj, f.fn, f.fint, f.ot} {
			x := d.FindObj(addr)
			if x != ObjNil {
				f.Edges = append(f.Edges, Edge{x, 0, addr - d.objects[x].Addr, ""})
			}
		}
	}
}

func nameFallback(d *Dump) {
	// No dwarf info, just name generically
	for _, t := range d.Types {
		for i := range t.Fields {
			t.Fields[i].Name = fmt.Sprintf("field%d", i)
		}
	}
	// name all frame fields
	for _, r := range d.Frames {
		for i := range r.Fields {
			r.Fields[i].Name = fmt.Sprintf("var%d", i)
		}
	}
	// name all globals
	for i := range d.Data.Fields {
		d.Data.Fields[i].Name = fmt.Sprintf("data%d", i)
	}
	for i := range d.Bss.Fields {
		d.Bss.Fields[i].Name = fmt.Sprintf("bss%d", i)
	}
}

func nameFullTypes(d *Dump) {
	for _, ft := range d.FTList {
		if ft.Type == nil {
			nameRaw(d, ft)
		} else {
			nameDwarf(d, ft)
		}
	}
}

func nameRaw(d *Dump, ft *FullType) {
	for i := 0; i < len(ft.GCSig); i++ {
		switch ft.GCSig[i] {
		case 'S':
			// TODO: byte arrays instead?
			if d.PtrSize == 8 {
				ft.Fields = append(ft.Fields, Field{FieldKindBytes8, uint64(i) * d.PtrSize, fmt.Sprintf("%d", i), ""})
			} else {
				ft.Fields = append(ft.Fields, Field{FieldKindBytes4, uint64(i) * d.PtrSize, fmt.Sprintf("%d", i), ""})
			}
		case 'P':
			ft.Fields = append(ft.Fields, Field{FieldKindPtr, uint64(i) * d.PtrSize, fmt.Sprintf("%d", i), ""})
		case 'I':
			ft.Fields = append(ft.Fields, Field{FieldKindIface, uint64(i) * d.PtrSize, fmt.Sprintf("%d", i), ""})
			i++
		case 'E':
			ft.Fields = append(ft.Fields, Field{FieldKindEface, uint64(i) * d.PtrSize, fmt.Sprintf("%d", i), ""})
			i++
		}
	}
	// after gc signature, there may be more data bytes
	for i := uint64(len(ft.GCSig)) * d.PtrSize; i < ft.Size; i += d.PtrSize {
		if d.PtrSize == 8 {
			ft.Fields = append(ft.Fields, Field{FieldKindBytes8, i, fmt.Sprintf("%d", i/d.PtrSize), ""})
		} else {
			ft.Fields = append(ft.Fields, Field{FieldKindBytes4, i, fmt.Sprintf("%d", i/d.PtrSize), ""})
		}
		if i >= 1<<16 {
			// ignore >64KB of data
			ft.Fields = append(ft.Fields, Field{FieldKindBytesElided, i, fmt.Sprintf("%d", i/d.PtrSize), ""})
			break
		}
	}
}
func nameDwarf(d *Dump, ft *FullType) {
	t := ft.Type
	for _, f := range t.dwarfFields() {
		switch typ := f.type_.(type) {
		case *dwarfPtrType:
			if typ.elem == nil {
				// TODO: viewer should escape <, so we can use that instead of &lt;
				ft.Fields = append(ft.Fields, Field{FieldKindPtr, f.offset, f.name, "&lt;untyped&gt;"})
			} else {
				ft.Fields = append(ft.Fields, Field{FieldKindPtr, f.offset, f.name, typ.elem.Name()})
			}
		case *dwarfBaseType:
			switch {
			case typ.encoding == dw_ate_boolean:
				ft.Fields = append(ft.Fields, Field{FieldKindBool, f.offset, f.name, ""})
			case typ.encoding == dw_ate_signed && typ.size == 1:
				ft.Fields = append(ft.Fields, Field{FieldKindSInt8, f.offset, f.name, ""})
			case typ.encoding == dw_ate_unsigned && typ.size == 1:
				ft.Fields = append(ft.Fields, Field{FieldKindUInt8, f.offset, f.name, ""})
			case typ.encoding == dw_ate_signed && typ.size == 2:
				ft.Fields = append(ft.Fields, Field{FieldKindSInt16, f.offset, f.name, ""})
			case typ.encoding == dw_ate_unsigned && typ.size == 2:
				ft.Fields = append(ft.Fields, Field{FieldKindUInt16, f.offset, f.name, ""})
			case typ.encoding == dw_ate_signed && typ.size == 4:
				ft.Fields = append(ft.Fields, Field{FieldKindSInt32, f.offset, f.name, ""})
			case typ.encoding == dw_ate_unsigned && typ.size == 4:
				ft.Fields = append(ft.Fields, Field{FieldKindUInt32, f.offset, f.name, ""})
			case typ.encoding == dw_ate_signed && typ.size == 8:
				ft.Fields = append(ft.Fields, Field{FieldKindSInt64, f.offset, f.name, ""})
			case typ.encoding == dw_ate_unsigned && typ.size == 8:
				ft.Fields = append(ft.Fields, Field{FieldKindUInt64, f.offset, f.name, ""})
			case typ.encoding == dw_ate_float && typ.size == 4:
				ft.Fields = append(ft.Fields, Field{FieldKindFloat32, f.offset, f.name, ""})
			case typ.encoding == dw_ate_float && typ.size == 8:
				ft.Fields = append(ft.Fields, Field{FieldKindFloat64, f.offset, f.name, ""})
			case typ.encoding == dw_ate_complex_float && typ.size == 8:
				ft.Fields = append(ft.Fields, Field{FieldKindComplex64, f.offset, f.name, ""})
			case typ.encoding == dw_ate_complex_float && typ.size == 16:
				ft.Fields = append(ft.Fields, Field{FieldKindComplex128, f.offset, f.name, ""})
			default:
				log.Fatalf("unknown encoding encoding=%d size=%d", typ.encoding, typ.size)
			}
		case *dwarfIfaceType:
			ft.Fields = append(ft.Fields, Field{FieldKindIface, f.offset, f.name, ""})
		case *dwarfEfaceType:
			ft.Fields = append(ft.Fields, Field{FieldKindEface, f.offset, f.name, ""})
		default:
			log.Fatalf("bad dwarf type %v", typ)
		}
	}
}

type byAddr []object

func (a byAddr) Len() int           { return len(a) }
func (a byAddr) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a byAddr) Less(i, j int) bool { return a[i].Addr < a[j].Addr }

func Read(dumpname, execname string) *Dump {
	d := rawRead(dumpname)
	link1(d)
	if execname != "" {
		typePropagate(d, execname)
		nameWithDwarf(d, execname)
	} else {
		nameFallback(d)
	}
	nameFullTypes(d)
	link2(d)
	return d
}

func readPtr(d *Dump, b []byte) uint64 {
	switch d.PtrSize {
	case 4:
		return uint64(d.Order.Uint32(b))
	case 8:
		return d.Order.Uint64(b)
	default:
		log.Fatal("unsupported PtrSize=%d", d.PtrSize)
		return 0
	}
}
