// Synchronous FIFO. 4 x 16 bit words.
//
typedef logic [7:0] ubyte;
typedef struct {
ubyte src;
ubyte dst;
ubyte [0:3] data;
} packet_t;

module fifo (
input clk,
input rstp,
input packet_t din,
input readp,
input writep,
output packet_t dout,
output logic emptyp,
output logic fullp
);
int i;
// Defines sizes in terms of bits.
//
parameter DEPTH = 2, // 2 bits, e.g. 4 words in the FIFO.
MAX_COUNT = (1<<DEPTH);// topmost address in FIFO.
// Define the FIFO pointers. A FIFO is essentially a circular queue.
//
reg [(DEPTH-1):0]tail;
reg [(DEPTH-1):0]head;
// Define the FIFO counter. Counts the number of entries in the FIFO which
// is how we figure out things like Empty and Full.
//
reg [(DEPTH):0]count;
// Define our regsiter bank. This is actually synthesizable!
//
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Array of structures
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
packet_t fifomem[0:MAX_COUNT];

// Dout is registered and gets the value that tail points to RIGHT NOW.
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Clear every element of fifomem
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
always_ff @(posedge clk) 
   if (rstp == 1) 
	dout <= {default:0};
   else 
	dout <= fifomem[tail];
		
// Update FIFO memory.
always_ff @(posedge clk)
   if (rstp == 1'b0 && writep == 1'b1 && fullp == 1'b0) 
	fifomem[head] <= din;

// Update the head register.
//
always_ff @(posedge clk)
   if (rstp == 1'b1) 
	head <= 0;
   else 
     	if (writep == 1'b1 && fullp == 1'b0) // WRITE
	   head <= head + 1;

// Update the tail register.
//
always_ff @(posedge clk) 
   if (rstp == 1'b1) 
	tail <= 0;
   else 
	if (readp == 1'b1 && emptyp == 1'b0) // READ
	    tail <= tail + 1;


// Update the count regsiter.
//
always_ff @(posedge clk) 
   if (rstp == 1'b1) 
	count <= 0;
   else 
	case ({readp, writep})
	  2'b00: count <= count;
	  2'b01: // WRITE
	      if (!fullp)
		 count <= count + 1;
	  2'b10: // READ
	      if (!emptyp)
		 count <= count - 1;
	  2'b11: // Concurrent read and write.. no change in count
	 	 count <= count;
	endcase

// *** Update the flags
//
// First, update the empty flag.
//
always_comb
   if (count == 0)
	emptyp = 1'b1;
   else
	emptyp = 1'b0;

// Update the full flag
//
always_comb
   if (count < MAX_COUNT)
	fullp = 1'b0;
   else
	fullp = 1'b1;

endmodule




