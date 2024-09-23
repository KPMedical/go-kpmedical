// Code generated by github.com/fjl/gencodec. DO NOT EDIT.

package engine

import (
	"encoding/json"
	"errors"

	"github.com/KPMedical/go-kpmedical/common"
	"github.com/KPMedical/go-kpmedical/common/hexutil"
	"github.com/KPMedical/go-kpmedical/core/types"
)

var _ = (*payloadAttributesMarshaling)(nil)

// MarshalJSON marshals as JSON.
func (p PayloadAttributes) MarshalJSON() ([]byte, error) {
	type PayloadAttributes struct {
		Timestamp             hexutil.Uint64      `json:"timestamp"             gencodec:"required"`
		Random                common.Hash         `json:"prevRandao"            gencodec:"required"`
		SuggestedFeeRecipient common.Address      `json:"suggestedFeeRecipient" gencodec:"required"`
		Withdrawals           []*types.Withdrawal `json:"withdrawals"`
		BeaconRoot            *common.Hash        `json:"parentBeaconBlockRoot"`
	}
	var enc PayloadAttributes
	enc.Timestamp = hexutil.Uint64(p.Timestamp)
	enc.Random = p.Random
	enc.SuggestedFeeRecipient = p.SuggestedFeeRecipient
	enc.Withdrawals = p.Withdrawals
	enc.BeaconRoot = p.BeaconRoot
	return json.Marshal(&enc)
}

// UnmarshalJSON unmarshals from JSON.
func (p *PayloadAttributes) UnmarshalJSON(input []byte) error {
	type PayloadAttributes struct {
		Timestamp             *hexutil.Uint64     `json:"timestamp"             gencodec:"required"`
		Random                *common.Hash        `json:"prevRandao"            gencodec:"required"`
		SuggestedFeeRecipient *common.Address     `json:"suggestedFeeRecipient" gencodec:"required"`
		Withdrawals           []*types.Withdrawal `json:"withdrawals"`
		BeaconRoot            *common.Hash        `json:"parentBeaconBlockRoot"`
	}
	var dec PayloadAttributes
	if err := json.Unmarshal(input, &dec); err != nil {
		return err
	}
	if dec.Timestamp == nil {
		return errors.New("missing required field 'timestamp' for PayloadAttributes")
	}
	p.Timestamp = uint64(*dec.Timestamp)
	if dec.Random == nil {
		return errors.New("missing required field 'prevRandao' for PayloadAttributes")
	}
	p.Random = *dec.Random
	if dec.SuggestedFeeRecipient == nil {
		return errors.New("missing required field 'suggestedFeeRecipient' for PayloadAttributes")
	}
	p.SuggestedFeeRecipient = *dec.SuggestedFeeRecipient
	if dec.Withdrawals != nil {
		p.Withdrawals = dec.Withdrawals
	}
	if dec.BeaconRoot != nil {
		p.BeaconRoot = dec.BeaconRoot
	}
	return nil
}
