// Code generated by github.com/fjl/gencodec. DO NOT EDIT.

package t8ntool

import (
	"encoding/json"
	"errors"
	"math/big"

	"github.com/KPMedical/go-kpmedical/common"
	"github.com/KPMedical/go-kpmedical/common/hexutil"
	"github.com/KPMedical/go-kpmedical/common/math"
	"github.com/KPMedical/go-kpmedical/core/types"
)

var _ = (*headerMarshaling)(nil)

// MarshalJSON marshals as JSON.
func (h header) MarshalJSON() ([]byte, error) {
	type header struct {
		ParentHash            common.Hash           `json:"parentHash"`
		OmmerHash             *common.Hash          `json:"sha3Uncles"`
		Coinbase              *common.Address       `json:"miner"`
		Root                  common.Hash           `json:"stateRoot"        gencodec:"required"`
		TxHash                *common.Hash          `json:"transactionsRoot"`
		ReceiptHash           *common.Hash          `json:"receiptsRoot"`
		Bloom                 types.Bloom           `json:"logsBloom"`
		Difficulty            *math.HexOrDecimal256 `json:"difficulty"`
		Number                *math.HexOrDecimal256 `json:"number"           gencodec:"required"`
		GasLimit              math.HexOrDecimal64   `json:"gasLimit"         gencodec:"required"`
		GasUsed               math.HexOrDecimal64   `json:"gasUsed"`
		Time                  math.HexOrDecimal64   `json:"timestamp"        gencodec:"required"`
		Extra                 hexutil.Bytes         `json:"extraData"`
		MixDigest             common.Hash           `json:"mixHash"`
		Nonce                 *types.BlockNonce     `json:"nonce"`
		BaseFee               *math.HexOrDecimal256 `json:"baseFeePerGas" rlp:"optional"`
		WithdrawalsHash       *common.Hash          `json:"withdrawalsRoot" rlp:"optional"`
		BlobGasUsed           *math.HexOrDecimal64  `json:"blobGasUsed"   rlp:"optional"`
		ExcessBlobGas         *math.HexOrDecimal64  `json:"excessBlobGas"   rlp:"optional"`
		ParentBeaconBlockRoot *common.Hash          `json:"parentBeaconBlockRoot" rlp:"optional"`
	}
	var enc header
	enc.ParentHash = h.ParentHash
	enc.OmmerHash = h.OmmerHash
	enc.Coinbase = h.Coinbase
	enc.Root = h.Root
	enc.TxHash = h.TxHash
	enc.ReceiptHash = h.ReceiptHash
	enc.Bloom = h.Bloom
	enc.Difficulty = (*math.HexOrDecimal256)(h.Difficulty)
	enc.Number = (*math.HexOrDecimal256)(h.Number)
	enc.GasLimit = math.HexOrDecimal64(h.GasLimit)
	enc.GasUsed = math.HexOrDecimal64(h.GasUsed)
	enc.Time = math.HexOrDecimal64(h.Time)
	enc.Extra = h.Extra
	enc.MixDigest = h.MixDigest
	enc.Nonce = h.Nonce
	enc.BaseFee = (*math.HexOrDecimal256)(h.BaseFee)
	enc.WithdrawalsHash = h.WithdrawalsHash
	enc.BlobGasUsed = (*math.HexOrDecimal64)(h.BlobGasUsed)
	enc.ExcessBlobGas = (*math.HexOrDecimal64)(h.ExcessBlobGas)
	enc.ParentBeaconBlockRoot = h.ParentBeaconBlockRoot
	return json.Marshal(&enc)
}

// UnmarshalJSON unmarshals from JSON.
func (h *header) UnmarshalJSON(input []byte) error {
	type header struct {
		ParentHash            *common.Hash          `json:"parentHash"`
		OmmerHash             *common.Hash          `json:"sha3Uncles"`
		Coinbase              *common.Address       `json:"miner"`
		Root                  *common.Hash          `json:"stateRoot"        gencodec:"required"`
		TxHash                *common.Hash          `json:"transactionsRoot"`
		ReceiptHash           *common.Hash          `json:"receiptsRoot"`
		Bloom                 *types.Bloom          `json:"logsBloom"`
		Difficulty            *math.HexOrDecimal256 `json:"difficulty"`
		Number                *math.HexOrDecimal256 `json:"number"           gencodec:"required"`
		GasLimit              *math.HexOrDecimal64  `json:"gasLimit"         gencodec:"required"`
		GasUsed               *math.HexOrDecimal64  `json:"gasUsed"`
		Time                  *math.HexOrDecimal64  `json:"timestamp"        gencodec:"required"`
		Extra                 *hexutil.Bytes        `json:"extraData"`
		MixDigest             *common.Hash          `json:"mixHash"`
		Nonce                 *types.BlockNonce     `json:"nonce"`
		BaseFee               *math.HexOrDecimal256 `json:"baseFeePerGas" rlp:"optional"`
		WithdrawalsHash       *common.Hash          `json:"withdrawalsRoot" rlp:"optional"`
		BlobGasUsed           *math.HexOrDecimal64  `json:"blobGasUsed"   rlp:"optional"`
		ExcessBlobGas         *math.HexOrDecimal64  `json:"excessBlobGas"   rlp:"optional"`
		ParentBeaconBlockRoot *common.Hash          `json:"parentBeaconBlockRoot" rlp:"optional"`
	}
	var dec header
	if err := json.Unmarshal(input, &dec); err != nil {
		return err
	}
	if dec.ParentHash != nil {
		h.ParentHash = *dec.ParentHash
	}
	if dec.OmmerHash != nil {
		h.OmmerHash = dec.OmmerHash
	}
	if dec.Coinbase != nil {
		h.Coinbase = dec.Coinbase
	}
	if dec.Root == nil {
		return errors.New("missing required field 'stateRoot' for header")
	}
	h.Root = *dec.Root
	if dec.TxHash != nil {
		h.TxHash = dec.TxHash
	}
	if dec.ReceiptHash != nil {
		h.ReceiptHash = dec.ReceiptHash
	}
	if dec.Bloom != nil {
		h.Bloom = *dec.Bloom
	}
	if dec.Difficulty != nil {
		h.Difficulty = (*big.Int)(dec.Difficulty)
	}
	if dec.Number == nil {
		return errors.New("missing required field 'number' for header")
	}
	h.Number = (*big.Int)(dec.Number)
	if dec.GasLimit == nil {
		return errors.New("missing required field 'gasLimit' for header")
	}
	h.GasLimit = uint64(*dec.GasLimit)
	if dec.GasUsed != nil {
		h.GasUsed = uint64(*dec.GasUsed)
	}
	if dec.Time == nil {
		return errors.New("missing required field 'timestamp' for header")
	}
	h.Time = uint64(*dec.Time)
	if dec.Extra != nil {
		h.Extra = *dec.Extra
	}
	if dec.MixDigest != nil {
		h.MixDigest = *dec.MixDigest
	}
	if dec.Nonce != nil {
		h.Nonce = dec.Nonce
	}
	if dec.BaseFee != nil {
		h.BaseFee = (*big.Int)(dec.BaseFee)
	}
	if dec.WithdrawalsHash != nil {
		h.WithdrawalsHash = dec.WithdrawalsHash
	}
	if dec.BlobGasUsed != nil {
		h.BlobGasUsed = (*uint64)(dec.BlobGasUsed)
	}
	if dec.ExcessBlobGas != nil {
		h.ExcessBlobGas = (*uint64)(dec.ExcessBlobGas)
	}
	if dec.ParentBeaconBlockRoot != nil {
		h.ParentBeaconBlockRoot = dec.ParentBeaconBlockRoot
	}
	return nil
}
