
class whdl_class_index_id #( type T = int , type IDX = int);

  static function IDX index_id( input T a );
    return a.index_id();
  endfunction : index_id

endclass : whdl_class_index_id

class whdl_built_in_index_id #( type T = int);
  static function T index_id( input T a);
    return a;
  endfunction : index_id
endclass : whdl_built_in_index_id

class whdl_ooo_comparator
  #(type T = int,
    type IDX = int,
    type index_id_type = whdl_class_index_id #(T) );

  typedef whdl_ooo_comparator #(T, IDX, index_id_type) this_type;

  typedef T q_of_T[$];
  typedef IDX q_of_IDX[$];

  mailbox #(Packet) mb_0;   // mailbox handle
  mailbox #(Packet) mb_1;   // mailbox handle

  bit before_queued = 0;
  bit after_queued = 0;

  protected int m_matches, m_mismatches;
  index_id_type m_idx_id_gen;

  protected q_of_T received_data[IDX];
  protected int rcv_count[IDX];

  protected process proc_1 = null;
  protected process proc_0  = null;
  
  protected task get_data(ref mailbox #(T) txn_fifo, ref process proc, input bit is_before);
    T txn_data, txn_existing;
    IDX idx;
    string rs;
    q_of_T tmpq;
    bit need_to_compare;
    forever begin
      proc = process::self();

   // Get the transaction object
      txn_fifo.get(txn_data);
      idx = index_id_type::index_id(txn_data);

   // Check to see if there is an existing object to compare
      need_to_compare = (rcv_count.exists(idx) &&
                         ((is_before && rcv_count[idx] > 0) ||
                         (!is_before && rcv_count[idx] < 0)));
      if (need_to_compare) begin
   // Compare objects
        tmpq = received_data[idx];
	txn_existing = tmpq.pop_front();
        received_data[idx] = tmpq;
        if (txn_data.compare(txn_existing))
          m_matches++;
        else begin
          m_mismatches++;
          $display("Compare Mismatch:\nExisting:%s\nReceived:%s",
                    txn_existing.convert2string(), txn_data.convert2string());
        end
      end
      else begin
      // If no compare happened, add the new entry
        if (received_data.exists(idx)) 
          tmpq = received_data[idx];
        else
          tmpq = {};
        tmpq.push_back(txn_data);
        received_data[idx] = tmpq;
      end

   // Update the index count
      if (is_before)
	if (rcv_count.exists(idx)) begin
	  rcv_count[idx]--;
        end
	else
	  rcv_count[idx] = -1;
      else
	if (rcv_count.exists(idx)) begin
	  rcv_count[idx]++;
        end
	else
	  rcv_count[idx] = 1;

   // If index count is balanced, remove entry from the arrays
      if (rcv_count[idx] == 0) begin
//        tmpq = received_data[idx];
//        assert(tmpq.size() == 0);
	received_data.delete(idx);
	rcv_count.delete(idx);
      end
    end // forever
  endtask

  virtual function int get_matches();
    return m_matches;
  endfunction : get_matches

  virtual function int get_mismatches();
    return m_mismatches;
  endfunction : get_mismatches

  virtual function int get_total_missing();
    int num_missing;
    foreach (rcv_count[i]) begin
      num_missing += (rcv_count[i] < 0 ? -rcv_count[i] : rcv_count[i]);
    end
    return num_missing;
  endfunction : get_total_missing
  
  virtual function q_of_IDX get_missing_indexes();
    q_of_IDX rv = rcv_count.find_index() with (item != 0);
    return rv;
  endfunction : get_missing_indexes;
  
  virtual function int get_missing_index_count(IDX i);
  // If count is < 0, more "before" txns were received
  // If count is > 0, more "after" txns were received
    if (rcv_count.exists(i))
      return rcv_count[i];
    else
      return 0;
  endfunction : get_missing_index_count;

  task run();
    fork
      get_data(mb_1, proc_1, 1);
      get_data(mb_0, proc_0, 0);
    join
  endtask

 virtual function void kill();
  proc_1.kill();
  proc_0.kill(); 
 endfunction 

endclass

